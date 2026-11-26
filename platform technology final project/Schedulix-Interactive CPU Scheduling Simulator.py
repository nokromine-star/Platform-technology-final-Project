from __future__ import annotations

import csv
import json
import math
import os
import random
import re
import struct
import tempfile
import threading
import tkinter as tk
import tkinter.font as tkfont
import wave
from collections import deque
from dataclasses import dataclass, replace
from tkinter import filedialog, messagebox, ttk
from typing import Callable, Deque, Dict, Iterable, List, Optional, Sequence, Tuple

try:  # winsound only exists on Windows; the app still works without it.
    import winsound
except ImportError:  # pragma: no cover - non-Windows
    winsound = None


# =============================================================================
# 1. DATA MODELS
# =============================================================================

IDLE = "IDLE"

Segment = Tuple[str, int, int]            # (pid or IDLE, start, end)
QuantumSlice = Tuple[str, int, int, int]  # (pid, start, end, remaining burst)


@dataclass(frozen=True)
class Process:
    """One process in the workload. `order` breaks ties (entry order)."""
    pid: str
    arrival: int
    burst: int
    order: int = 0


@dataclass(frozen=True)
class Metrics:
    """Per-process results of one algorithm."""
    arrival: int
    burst: int
    first_start: int
    completion: int

    @property
    def turnaround(self) -> int:   # TAT = CT - AT
        return self.completion - self.arrival

    @property
    def waiting(self) -> int:      # WT = TAT - BT
        return self.turnaround - self.burst

    @property
    def response(self) -> int:     # RT = first start - AT
        return self.first_start - self.arrival


@dataclass(frozen=True)
class Summary:
    """Workload-level statistics of one algorithm."""
    avg_tat: float
    avg_wt: float
    avg_rt: float
    max_wt: int
    makespan: int
    busy: int
    idle: int
    utilization: float      # percent
    throughput: float       # processes per time unit
    context_switches: int


@dataclass
class Result:
    key: str                # short id: FCFS / SJF / SRTF / RR
    name: str               # long display name
    timeline: List[Segment]
    metrics: Dict[str, Metrics]
    quantum_log: List[QuantumSlice]
    summary: Summary


# =============================================================================
# 2. SCHEDULING ALGORITHMS
# =============================================================================

def _append_segment(timeline: List[Segment], pid: str, start: int, end: int) -> None:
    """Add a Gantt segment, merging it with the previous one if contiguous."""
    if end <= start:
        return
    if timeline and timeline[-1][0] == pid and timeline[-1][2] == start:
        old_pid, old_start, _ = timeline[-1]
        timeline[-1] = (old_pid, old_start, end)
    else:
        timeline.append((pid, start, end))


def _by_arrival(processes: Sequence[Process]) -> List[Process]:
    return sorted(processes, key=lambda p: (p.arrival, p.order))


def _count_context_switches(timeline: Sequence[Segment]) -> int:
    """Number of times the CPU is handed to a *different* process.

    Idle gaps are ignored, and a process that keeps the CPU across merged
    slices is not counted as a switch.
    """
    switches, previous = 0, None
    for pid, _, _ in timeline:
        if pid == IDLE:
            continue
        if previous is not None and pid != previous:
            switches += 1
        previous = pid
    return switches


def _finish(key: str, name: str, processes: Sequence[Process],
            timeline: List[Segment], log: List[QuantumSlice]) -> Result:
    """Turn a raw timeline into metrics + summary and wrap it in a Result."""
    first_start: Dict[str, int] = {}
    completion: Dict[str, int] = {}
    for pid, start, end in timeline:
        if pid == IDLE:
            continue
        first_start.setdefault(pid, start)
        completion[pid] = end

    metrics = {
        p.pid: Metrics(p.arrival, p.burst, first_start[p.pid], completion[p.pid])
        for p in processes if p.pid in completion
    }
    n = max(len(metrics), 1)
    makespan = timeline[-1][2] if timeline else 0
    idle = sum(e - s for pid, s, e in timeline if pid == IDLE)
    busy = makespan - idle
    summary = Summary(
        avg_tat=sum(m.turnaround for m in metrics.values()) / n,
        avg_wt=sum(m.waiting for m in metrics.values()) / n,
        avg_rt=sum(m.response for m in metrics.values()) / n,
        max_wt=max((m.waiting for m in metrics.values()), default=0),
        makespan=makespan, busy=busy, idle=idle,
        utilization=100.0 * busy / makespan if makespan else 0.0,
        throughput=len(metrics) / makespan if makespan else 0.0,
        context_switches=_count_context_switches(timeline),
    )
    return Result(key, name, timeline, metrics, log, summary)


def fcfs(processes: Sequence[Process]) -> Result:
    """First Come, First Served: non-preemptive, strictly by arrival."""
    t, timeline = 0, []
    for p in _by_arrival(processes):
        if t < p.arrival:
            _append_segment(timeline, IDLE, t, p.arrival)
            t = p.arrival
        _append_segment(timeline, p.pid, t, t + p.burst)
        t += p.burst
    return _finish("FCFS", "FCFS", processes, timeline, [])


def sjf(processes: Sequence[Process]) -> Result:
    """Shortest Job First (non-preemptive): shortest ready burst runs to the end."""
    waiting = list(processes)
    t, timeline = 0, []
    while waiting:
        ready = [p for p in waiting if p.arrival <= t]
        if not ready:
            nxt = min(p.arrival for p in waiting)
            _append_segment(timeline, IDLE, t, nxt)
            t = nxt
            continue
        p = min(ready, key=lambda x: (x.burst, x.arrival, x.order))
        _append_segment(timeline, p.pid, t, t + p.burst)
        t += p.burst
        waiting.remove(p)
    return _finish("SJF", "SJF (Non-preemptive)", processes, timeline, [])


def srtf(processes: Sequence[Process]) -> Result:
    """Shortest Remaining Time First (preemptive SJF).

    Event driven: the chosen process runs until it finishes or until the next
    arrival, whichever comes first, because only an arrival can change the
    decision. This gives the same schedule as ticking one unit at a time.
    """
    remaining = {p.pid: p.burst for p in processes}
    pending = _by_arrival(processes)
    ready: List[Process] = []
    t, i, timeline = 0, 0, []
    while i < len(pending) or ready:
        while i < len(pending) and pending[i].arrival <= t:
            ready.append(pending[i])
            i += 1
        if not ready:
            nxt = pending[i].arrival
            _append_segment(timeline, IDLE, t, nxt)
            t = nxt
            continue
        p = min(ready, key=lambda x: (remaining[x.pid], x.arrival, x.order))
        run = remaining[p.pid]
        if i < len(pending):
            run = min(run, pending[i].arrival - t)
        _append_segment(timeline, p.pid, t, t + run)
        t += run
        remaining[p.pid] -= run
        if remaining[p.pid] == 0:
            ready.remove(p)
    return _finish("SRTF", "SRTF (Preemptive)", processes, timeline, [])


def round_robin(processes: Sequence[Process], quantum: int) -> Result:
    """Round Robin with a fixed time quantum.

    Convention: processes that arrive during a slice join the ready queue
    *before* the preempted process is re-queued.
    """
    remaining = {p.pid: p.burst for p in processes}
    pending = _by_arrival(processes)
    ready: Deque[Process] = deque()
    timeline: List[Segment] = []
    log: List[QuantumSlice] = []
    t, i = 0, 0

    def admit() -> None:
        nonlocal i
        while i < len(pending) and pending[i].arrival <= t:
            ready.append(pending[i])
            i += 1

    while i < len(pending) or ready:
        admit()
        if not ready:
            nxt = pending[i].arrival
            _append_segment(timeline, IDLE, t, nxt)
            t = nxt
            continue
        p = ready.popleft()
        run = min(quantum, remaining[p.pid])
        start, t = t, t + run
        _append_segment(timeline, p.pid, start, t)
        remaining[p.pid] -= run
        admit()
        log.append((p.pid, start, t, remaining[p.pid]))
        if remaining[p.pid] > 0:
            ready.append(p)
    return _finish("RR", "Round Robin", processes, timeline, log)


def simulate(processes: Sequence[Process], quantum: int) -> List[Result]:
    """Run all four algorithms on the same workload."""
    return [fcfs(processes), sjf(processes), srtf(processes),
            round_robin(processes, quantum)]


# =============================================================================
# 3. VALIDATION & STORAGE
# =============================================================================

MAX_PROCESSES = 20
MAX_TIME = 999
MAX_QUANTUM = 99
PID_PATTERN = re.compile(r"^[A-Z0-9_-]{1,8}$")


class ValidationError(ValueError):
    """Invalid user input. `field` names the form field to highlight."""

    def __init__(self, field: str, message: str):
        super().__init__(message)
        self.field = field


def _parse_int(text: str, field: str, label: str, low: int, high: int) -> int:
    try:
        value = int(str(text).strip())
    except ValueError:
        raise ValidationError(field, f"{label} must be a whole number.") from None
    if not low <= value <= high:
        raise ValidationError(field, f"{label} must be between {low} and {high}.")
    return value


def validate_process(pid_text: str, arrival_text: str, burst_text: str,
                     taken: Iterable[str]) -> Tuple[str, int, int]:
    """Validate form input and return (pid, arrival, burst)."""
    pid = str(pid_text).strip().upper()
    if not PID_PATTERN.match(pid):
        raise ValidationError(
            "pid", "Process ID: 1-8 letters, digits, '_' or '-' (e.g. P1).")
    if pid == IDLE:
        raise ValidationError("pid", f"'{IDLE}' is reserved for CPU idle time.")
    if pid in set(taken):
        raise ValidationError("pid", f"A process named {pid} already exists.")
    arrival = _parse_int(arrival_text, "arrival", "Arrival", 0, MAX_TIME)
    burst = _parse_int(burst_text, "burst", "Burst", 1, MAX_TIME)
    return pid, arrival, burst


def validate_quantum(text: str) -> int:
    return _parse_int(text, "quantum", "Quantum", 1, MAX_QUANTUM)


def workload_to_dict(processes: Sequence[Process], quantum: int) -> dict:
    return {
        "app": "Schedulix", "version": 1, "quantum": quantum,
        "processes": [{"pid": p.pid, "arrival": p.arrival, "burst": p.burst}
                      for p in processes],
    }


def workload_from_dict(data: dict) -> Tuple[List[Process], int]:
    """Parse and validate a workload dict. Raises ValueError with a clear message."""
    if not isinstance(data, dict) or not isinstance(data.get("processes"), list):
        raise ValueError("This file is not a Schedulix workload.")
    items = data["processes"]
    if not items:
        raise ValueError("The workload contains no processes.")
    if len(items) > MAX_PROCESSES:
        raise ValueError(f"A workload can hold at most {MAX_PROCESSES} processes.")
    processes: List[Process] = []
    for index, item in enumerate(items):
        try:
            pid, at, bt = validate_process(
                item.get("pid", ""), item.get("arrival", ""), item.get("burst", ""),
                [p.pid for p in processes])
        except (ValidationError, AttributeError) as exc:
            raise ValueError(f"Process #{index + 1}: {exc}") from None
        processes.append(Process(pid, at, bt, index))
    quantum = validate_quantum(data.get("quantum", 2))
    return processes, quantum


def export_results_csv(path: str, results: Sequence[Result],
                       processes: Sequence[Process]) -> None:
    """Write per-process metrics, summaries and Gantt segments to one CSV file."""
    with open(path, "w", newline="", encoding="utf-8") as handle:
        out = csv.writer(handle)
        out.writerow(["Schedulix results"])
        out.writerow([])
        out.writerow(["PROCESS METRICS"])
        out.writerow(["Algorithm", "Process", "AT", "BT", "CT", "TAT", "WT", "RT"])
        for r in results:
            for p in processes:
                m = r.metrics[p.pid]
                out.writerow([r.name, p.pid, m.arrival, m.burst, m.completion,
                              m.turnaround, m.waiting, m.response])
        out.writerow([])
        out.writerow(["SUMMARY"])
        out.writerow(["Algorithm", "Avg TAT", "Avg WT", "Avg RT", "Max WT",
                      "CPU utilization %", "Throughput (proc/unit)",
                      "Context switches", "Makespan"])
        for r in results:
            s = r.summary
            out.writerow([r.name, f"{s.avg_tat:.2f}", f"{s.avg_wt:.2f}",
                          f"{s.avg_rt:.2f}", s.max_wt, f"{s.utilization:.1f}",
                          f"{s.throughput:.3f}", s.context_switches, s.makespan])
        out.writerow([])
        out.writerow(["GANTT TIMELINE"])
        out.writerow(["Algorithm", "Process", "Start", "End"])
        for r in results:
            for pid, start, end in r.timeline:
                out.writerow([r.name, pid, start, end])


# -- remembered preferences + last workload (stored in the user's home folder) --

SETTINGS_PATH = os.path.join(os.path.expanduser("~"), ".schedulix_settings.json")
DEFAULT_SETTINGS = {"fullscreen": True, "autorun": True, "sound": True,
                    "animate": True, "live": False}


def load_settings() -> dict:
    """Read saved preferences; any problem simply falls back to the defaults."""
    try:
        with open(SETTINGS_PATH, encoding="utf-8") as handle:
            data = json.load(handle)
    except (OSError, ValueError):
        return dict(DEFAULT_SETTINGS)
    return {**DEFAULT_SETTINGS, **(data if isinstance(data, dict) else {})}


def save_settings(data: dict) -> None:
    try:
        with open(SETTINGS_PATH, "w", encoding="utf-8") as handle:
            json.dump(data, handle, indent=2)
    except OSError:
        pass            # preferences are a convenience, never a reason to crash


# =============================================================================
# 4. SOUND (generated at runtime, Windows only, silently disabled elsewhere)
# =============================================================================

def build_music_wav(path: str) -> None:
    """Synthesize a short looping melody with the standard library only."""
    rate = 22050
    melody = [(261.63, .30), (329.63, .30), (392.00, .30), (329.63, .30),
              (293.66, .30), (349.23, .30), (440.00, .30), (349.23, .30)]
    frames = bytearray()
    for freq, duration in melody:
        count = int(rate * duration)
        for n in range(count):
            fade = min(1.0, n / 500, (count - n) / 500)
            value = int(1700 * fade * math.sin(2 * math.pi * freq * n / rate))
            frames.extend(struct.pack("<h", value))
    with wave.open(path, "wb") as wav:
        wav.setnchannels(1)
        wav.setsampwidth(2)
        wav.setframerate(rate)
        wav.writeframes(bytes(frames))


class SoundManager:
    """Background music and a click sound. Everything is a no-op if unsupported."""

    def __init__(self, enabled: bool = True) -> None:
        self.available = winsound is not None
        self.enabled = enabled
        self.music_file: Optional[str] = None
        if self.available:
            try:
                handle = tempfile.NamedTemporaryFile(
                    prefix="schedulix_", suffix=".wav", delete=False)
                self.music_file = handle.name
                handle.close()
                build_music_wav(self.music_file)
            except (OSError, wave.Error):
                self.music_file = None

    def start_music(self) -> None:
        if self.enabled and self.music_file and winsound:
            try:
                winsound.PlaySound(self.music_file, winsound.SND_FILENAME
                                   | winsound.SND_ASYNC | winsound.SND_LOOP)
            except RuntimeError:
                self.available = False

    def stop_music(self) -> None:
        if winsound:
            try:
                winsound.PlaySound(None, winsound.SND_PURGE)
            except RuntimeError:
                pass

    def toggle(self) -> bool:
        """Switch sound on/off and return the new state."""
        self.enabled = not self.enabled
        self.start_music() if self.enabled else self.stop_music()
        return self.enabled

    def click(self) -> None:
        """Short UI click, played on a thread so the interface never stalls."""
        if not (self.enabled and winsound):
            return

        def beep() -> None:
            try:
                winsound.Beep(850, 28)
            except RuntimeError:
                pass
        threading.Thread(target=beep, daemon=True).start()

    def cleanup(self) -> None:
        self.stop_music()
        if self.music_file and os.path.exists(self.music_file):
            try:
                os.unlink(self.music_file)
            except OSError:
                pass


# =============================================================================
# 5. THEME & REUSABLE WIDGETS
# =============================================================================

BG = "#080F1C"          # deep midnight
PANEL = "#111D2E"       # raised surface
PANEL_2 = "#1A2A40"     # controls / secondary surface
PANEL_ALT = "#0F1A2B"   # zebra rows
TEXT = "#F3F7FC"
MUTED = "#91A3B8"
ACCENT = "#48E0C0"
ACCENT_2 = "#FFBE6B"
DANGER = "#FF7A8A"
BORDER = "#263A52"
IDLE_COLOR = "#52636b"

PALETTE = ["#63d6bd", "#7ca9f5", "#f3b562", "#d69bea", "#f28f8f", "#91c98b",
           "#e6a66b", "#8bc7d9", "#c3b1f5", "#f0d86b", "#ef8fc0", "#9fb4c8"]

ALGO_COLORS = {"FCFS": "#63d6bd", "SJF": "#7ca9f5",
               "SRTF": "#f3b562", "RR": "#d69bea"}
METRIC_COLORS = {"TAT": "#7ca9f5", "WT": "#f3b562", "RT": "#63d6bd"}

_UI_FONT = "Segoe UI"
_MONO_FONT = "Consolas"


def init_fonts(root: tk.Misc) -> None:
    """Pick the best installed fonts (call once after the Tk root exists)."""
    global _UI_FONT, _MONO_FONT
    families = set(tkfont.families(root))
    _UI_FONT = next((f for f in ("Segoe UI", "SF Pro Text", "Helvetica Neue",
                                 "Ubuntu", "DejaVu Sans") if f in families), "TkDefaultFont")
    _MONO_FONT = next((f for f in ("Cascadia Code", "Consolas", "Menlo",
                                   "DejaVu Sans Mono") if f in families), "TkFixedFont")


def font(size: int = 10, bold: bool = False) -> tuple:
    return (_UI_FONT, size, "bold") if bold else (_UI_FONT, size)


def mono(size: int = 9) -> tuple:
    return (_MONO_FONT, size)


def make_label(parent: tk.Misc, text: str, size: int = 10, color: str = TEXT,
               bold: bool = False, **kw) -> tk.Label:
    return tk.Label(parent, text=text, bg=parent.cget("bg"), fg=color,
                    font=font(size, bold), **kw)


def make_entry(parent: tk.Misc, width: int = 10, **kw) -> tk.Entry:
    return tk.Entry(parent, width=width, bg="#0d171e", fg=TEXT,
                    insertbackground=TEXT, relief="flat", font=font(10),
                    highlightthickness=1, highlightbackground="#36505d",
                    highlightcolor=ACCENT, **kw)


def mark_invalid(widget: tk.Widget, invalid: bool) -> None:
    """Outline an entry in red (or restore its normal outline)."""
    widget.configure(highlightbackground=DANGER if invalid else "#36505d",
                     highlightcolor=DANGER if invalid else ACCENT)


class FlatButton(tk.Button):
    """Flat button with hover feedback. kind: primary | secondary | danger."""

    STYLES = {
        "primary": (ACCENT, BG, "#8BEED8", ACCENT),
        "secondary": (PANEL_2, TEXT, "#29415D", BORDER),
        "danger": (PANEL_2, DANGER, "#3B2431", BORDER),
    }

    def __init__(self, parent: tk.Misc, text: str, command: Callable[[], None],
                 kind: str = "secondary", pad: Tuple[int, int] = (14, 9)):
        bg, fg, hover, border = self.STYLES[kind]
        super().__init__(parent, text=text, command=command, bg=bg, fg=fg,
                         activebackground=hover, activeforeground=fg,
                         disabledforeground="#4C5E73", relief="flat", bd=0,
                         padx=pad[0], pady=pad[1], cursor="hand2",
                         font=font(9, True), highlightthickness=1,
                         highlightbackground=border)
        self._bg, self._hover = bg, hover
        self.bind("<Enter>", lambda _e: self._tint(self._hover))
        self.bind("<Leave>", lambda _e: self._tint(self._bg))

    def _tint(self, color: str) -> None:
        if str(self["state"]) != "disabled":
            self.configure(bg=color)

    def set_enabled(self, enabled: bool) -> None:
        self.configure(state="normal" if enabled else "disabled",
                       cursor="hand2" if enabled else "arrow", bg=self._bg)


class KpiTile(tk.Frame):
    """A small stat card: caption, big value, optional sub-caption."""

    def __init__(self, parent: tk.Misc, caption: str, accent: str = ACCENT):
        super().__init__(parent, bg=PANEL, highlightthickness=1,
                         highlightbackground=BORDER)
        tk.Frame(self, bg=accent, height=3).pack(fill="x")
        make_label(self, caption.upper(), 7, MUTED, True).pack(
            anchor="w", padx=12, pady=(9, 0))
        self.value = make_label(self, "—", 17, TEXT, True)
        self.value.pack(anchor="w", padx=12)
        self.sub = make_label(self, " ", 8, MUTED)
        self.sub.pack(anchor="w", padx=12, pady=(0, 9))

    def set(self, value: str, sub: str = " ") -> None:
        self.value.config(text=value)
        self.sub.config(text=sub or " ")


class ScrollFrame(tk.Frame):
    """A vertically scrollable frame. Put your widgets into `.body`.

    The mouse wheel only scrolls the frame that is under the pointer, and
    leaves inner tables / text boxes alone when they can scroll themselves.
    """

    def __init__(self, parent: tk.Misc, bg: str = BG):
        super().__init__(parent, bg=bg)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0)
        self.bar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.bar.set)
        self.bar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.body = tk.Frame(self.canvas, bg=bg)
        self._window = self.canvas.create_window((0, 0), window=self.body, anchor="nw")
        self.body.bind("<Configure>", lambda _e: self.canvas.configure(
            scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda e: self.canvas.itemconfigure(
            self._window, width=e.width))
        self.bind("<Enter>", self._grab_wheel)
        self.bind("<Leave>", self._release_wheel)

    def _grab_wheel(self, _event=None) -> None:
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.bind_all(seq, self._on_wheel)

    def _release_wheel(self, _event=None) -> None:
        # <Leave> also fires when entering a child widget; only release for real.
        try:
            widget = self.winfo_containing(*self.winfo_pointerxy())
        except (KeyError, tk.TclError):
            widget = None
        while widget is not None:
            if widget is self:
                return
            widget = getattr(widget, "master", None)
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.unbind_all(seq)

    def _on_wheel(self, event) -> None:
        inner = event.widget
        if isinstance(inner, (ttk.Treeview, tk.Text)) and inner.yview() != (0.0, 1.0):
            return
        if self.body.winfo_reqheight() <= self.canvas.winfo_height():
            return
        if event.num == 4:
            step = -1
        elif event.num == 5:
            step = 1
        else:
            step = -1 if event.delta > 0 else 1
        self.canvas.yview_scroll(step * 2, "units")


def make_tree(parent: tk.Misc, columns: Sequence[Tuple[str, str, int]],
              height: int = 5, stretch: bool = False) -> ttk.Treeview:
    """Create a styled Treeview. columns = [(id, heading, width), ...]."""
    tree = ttk.Treeview(parent, columns=[c[0] for c in columns],
                        show="headings", height=height)
    for col_id, heading, width in columns:
        tree.heading(col_id, text=heading)
        tree.column(col_id, width=width, anchor="center", stretch=stretch)
    tree.tag_configure("odd", background=PANEL_ALT)
    tree.tag_configure("worst", foreground=ACCENT_2)
    return tree


def clear_tree(tree: ttk.Treeview) -> None:
    tree.delete(*tree.get_children())


def section_header(parent: tk.Misc, text: str, right: Optional[tk.Widget] = None,
                   padx: int = 20, pady: Tuple[int, int] = (6, 7)) -> tk.Frame:
    row = tk.Frame(parent, bg=parent.cget("bg"))
    row.pack(fill="x", padx=padx, pady=pady)
    make_label(row, text, 9, ACCENT, True).pack(side="left")
    return row


# =============================================================================
# 6. CHARTS
# =============================================================================

def nice_scale(max_value: float, ticks: int = 4) -> Tuple[float, float]:
    """Return (axis_top, step) so gridlines land on round numbers."""
    if max_value <= 0:
        return 1.0, 0.25
    raw = max_value / ticks
    magnitude = 10 ** math.floor(math.log10(raw))
    step = magnitude
    for multiple in (1, 2, 2.5, 5, 10):
        step = multiple * magnitude
        if step >= raw:
            break
    return math.ceil(max_value / step) * step, step


class GanttChart(tk.Canvas):
    """Animated Gantt chart with hover tooltips, time axis and legend."""

    TOP, BLOCK_H = 36, 46

    def __init__(self, parent: tk.Misc, color_for: Callable[[str], str]):
        super().__init__(parent, height=150, bg=PANEL, highlightthickness=0, bd=0)
        self.color_for = color_for
        self.timeline: List[Segment] = []
        self._job: Optional[str] = None
        self._resize_job: Optional[str] = None
        self._token = 0
        self._last_width = 0
        self.bind("<Configure>", self._on_resize)

    # -- public API ---------------------------------------------------------
    def show(self, timeline: Sequence[Segment], animate: bool = True) -> None:
        self.timeline = list(timeline)
        self._render(animate)

    def replay(self) -> None:
        self._render(True)

    def clear(self) -> None:
        self.timeline = []
        self._cancel()
        self.delete("all")

    # -- internals ----------------------------------------------------------
    def _cancel(self) -> None:
        self._token += 1
        if self._job is not None:
            self.after_cancel(self._job)
            self._job = None

    def _on_resize(self, event) -> None:
        if event.width == self._last_width:      # height-only change (legend rows)
            return
        if self._resize_job is not None:
            self.after_cancel(self._resize_job)
        animating = self._job is not None
        self._resize_job = self.after(120, lambda: self._render(animating))

    def _color(self, pid: str) -> str:
        return IDLE_COLOR if pid == IDLE else self.color_for(pid)

    def _visible_labels(self, left: float, usable: float, total: int) -> set:
        """Choose which time labels fit without overlapping (always keep the end)."""
        times = sorted({t for _, s, e in self.timeline for t in (s, e)})
        kept: List[int] = []
        last_x = -1e9
        for t in times:
            x = left + usable * t / total
            if x - last_x >= 24:
                kept.append(t)
                last_x = x
        end = times[-1]
        if kept[-1] != end:
            if len(kept) > 1:
                kept.pop()
            kept.append(end)
        return set(kept)

    def _render(self, animate: bool) -> None:
        self._cancel()
        self.delete("all")
        if not self.timeline:
            return
        width = max(self.winfo_width(), 420)
        self._last_width = self.winfo_width()
        left, right = 16, width - 16
        usable = right - left
        total = max(self.timeline[-1][2], 1)
        labels = self._visible_labels(left, usable, total)

        legend_bottom = self._draw_legend(left, right)
        if int(self["height"]) != legend_bottom:
            self.configure(height=legend_bottom)

        count = len(self.timeline)
        delay = max(30, min(170, int(2400 / count)))

        def draw(i: int) -> None:
            pid, start, end = self.timeline[i]
            x1 = left + usable * start / total
            x2 = max(left + usable * end / total, x1 + 1)
            tag = f"seg{i}"
            rect_tag = f"rect{i}"          # only rectangles have an outline option
            self.create_rectangle(x1, self.TOP, x2, self.TOP + self.BLOCK_H,
                                  fill=self._color(pid), outline=BG, width=2,
                                  tags=(tag, rect_tag))
            if x2 - x1 >= 26:
                self.create_text((x1 + x2) / 2, self.TOP + self.BLOCK_H / 2,
                                 text="idle" if pid == IDLE else pid, fill=BG,
                                 font=font(9, True), tags=(tag,))
            for t in ((start, end) if i == count - 1 else (start,)):
                x = left + usable * t / total
                self.create_line(x, self.TOP + self.BLOCK_H, x,
                                 self.TOP + self.BLOCK_H + 4, fill=MUTED)
                if t in labels:
                    self.create_text(x, self.TOP + self.BLOCK_H + 7, text=str(t),
                                     fill=MUTED, anchor="n", font=font(8))
            name = "CPU idle" if pid == IDLE else pid
            tip = f"{name}   {start} → {end}   ({end - start} units)"
            self.tag_bind(tag, "<Enter>", lambda _e, t=rect_tag: self.itemconfigure(
                t, outline="#FFFFFF"))
            self.tag_bind(tag, "<Leave>", lambda _e, t=rect_tag: (
                self.itemconfigure(t, outline=BG), self.delete("tip")))
            self.tag_bind(tag, "<Motion>", lambda e, s=tip: self._show_tip(e.x, s))

        if not animate:
            for i in range(count):
                draw(i)
            return

        token = self._token

        def step(i: int) -> None:
            if token != self._token or i >= count:
                return
            draw(i)
            self._job = self.after(delay, lambda: step(i + 1))
        step(0)

    def _draw_legend(self, left: float, right: float) -> int:
        """Draw the legend row(s); return the canvas height needed."""
        seen: List[str] = []
        for pid, _, _ in self.timeline:
            if pid not in seen:
                seen.append(pid)
        x, y = left, self.TOP + self.BLOCK_H + 36
        for pid in seen:
            label = "Idle" if pid == IDLE else pid
            item_w = 28 + len(label) * 7
            if x + item_w > right and x > left:
                x, y = left, y + 20
            self.create_rectangle(x, y, x + 11, y + 11, fill=self._color(pid),
                                  outline="")
            self.create_text(x + 17, y + 5, text=label, fill=MUTED, anchor="w",
                             font=font(8))
            x += item_w + 6
        return y + 28

    def _show_tip(self, x: float, text: str) -> None:
        self.delete("tip")
        width = max(self.winfo_width(), 420)
        x = min(max(x, 90), width - 90)
        label = self.create_text(x, self.TOP - 9, text=text, fill=TEXT,
                                 anchor="s", font=font(9, True), tags="tip")
        x1, y1, x2, y2 = self.bbox(label)
        box = self.create_rectangle(x1 - 8, y1 - 4, x2 + 8, y2 + 4, fill="#0B1424",
                                    outline=ACCENT, tags="tip")
        self.tag_raise(label, box)


class BarChart(tk.Canvas):
    """Grouped bar chart with animated growth, grid, axis and legend."""

    LEFT, RIGHT, TOP, BOTTOM = 48, 18, 40, 34

    def __init__(self, parent: tk.Misc, height: int = 300):
        super().__init__(parent, height=height, bg=PANEL, highlightthickness=1,
                         highlightbackground=BORDER, bd=0)
        self.categories: List[str] = []
        self.series: List[Tuple[str, str, List[float]]] = []
        self.fmt = "{:g}"
        self.empty_text = "Run the simulation to see this chart."
        self._progress = 1.0
        self._job: Optional[str] = None
        self.bind("<Configure>", lambda _e: self._draw())

    def set_data(self, categories: Sequence[str],
                 series: Sequence[Tuple[str, str, Sequence[float]]],
                 fmt: str = "{:g}", animate: bool = True) -> None:
        """series = [(label, colour, [value per category]), ...]"""
        self.categories = list(categories)
        self.series = [(n, c, list(v)) for n, c, v in series]
        self.fmt = fmt
        if self._job is not None:
            self.after_cancel(self._job)
            self._job = None
        self._progress = 0.0 if animate else 1.0
        self._draw()
        if animate:
            self._step()

    def clear(self) -> None:
        self.set_data([], [], animate=False)

    def _step(self) -> None:
        self._progress = min(1.0, self._progress + 0.08)
        self._draw()
        if self._progress < 1.0:
            self._job = self.after(16, self._step)
        else:
            self._job = None

    def _draw(self) -> None:
        self.delete("all")
        width, height = max(self.winfo_width(), 300), max(self.winfo_height(), 200)
        if not self.categories or not self.series:
            self.create_text(width / 2, height / 2, text=self.empty_text,
                             fill=MUTED, font=font(10))
            return
        plot_l, plot_r = self.LEFT, width - self.RIGHT
        plot_t, plot_b = self.TOP, height - self.BOTTOM
        top, step = nice_scale(max(max(v) for _, _, v in self.series))
        ease = 1 - (1 - self._progress) ** 3

        # Grid + y axis labels
        value = 0.0
        while value <= top + 1e-9:
            y = plot_b - (plot_b - plot_t) * value / top
            self.create_line(plot_l, y, plot_r, y, fill=BORDER if value else MUTED)
            self.create_text(plot_l - 8, y, text=f"{value:g}", fill=MUTED,
                             anchor="e", font=font(8))
            value += step

        # Bars
        group_w = (plot_r - plot_l) / len(self.categories)
        bar_w = min(group_w * 0.76 / len(self.series), 44)
        show_values = bar_w >= 15
        for gi, category in enumerate(self.categories):
            center = plot_l + group_w * (gi + 0.5)
            x0 = center - bar_w * len(self.series) / 2
            for si, (_, color, values) in enumerate(self.series):
                x1 = x0 + si * bar_w
                bar_h = (plot_b - plot_t) * values[gi] / top * ease
                self.create_rectangle(x1 + 1, plot_b - bar_h, x1 + bar_w - 1, plot_b,
                                      fill=color, outline="")
                if show_values and self._progress >= 1.0:
                    self.create_text(x1 + bar_w / 2, plot_b - bar_h - 3,
                                     text=self.fmt.format(values[gi]), fill=TEXT,
                                     anchor="s", font=font(8))
            self.create_text(center, plot_b + 9, text=category, fill=MUTED,
                             anchor="n", font=font(9, True))

        # Legend
        x = plot_l
        for label, color, _ in self.series:
            self.create_rectangle(x, 14, x + 11, 25, fill=color, outline="")
            self.create_text(x + 17, 19, text=label, fill=MUTED, anchor="w",
                             font=font(9))
            x += 40 + len(label) * 7


# =============================================================================
# 7. RESULT TABS
# =============================================================================

@dataclass(frozen=True)
class AlgoSpec:
    key: str
    tab_title: str
    heading: str
    subtitle: str


ALGORITHMS = (
    AlgoSpec("FCFS", "FCFS", "First Come, First Served",
             "Non-preemptive · processes run strictly in arrival order"),
    AlgoSpec("SJF", "SJF", "Shortest Job First",
             "Non-preemptive · the shortest ready burst runs to completion"),
    AlgoSpec("SRTF", "SRTF", "Shortest Remaining Time First",
             "Preemptive · the process with the least remaining work always runs"),
    AlgoSpec("RR", "ROUND ROBIN", "Round Robin",
             "Preemptive · each process gets a fixed time slice in turn"),
)


def build_calculation_lines(result: Result,
                            processes: Sequence[Process]) -> List[Tuple[str, str]]:
    """Step-by-step formulas as (text, style_tag) pairs."""
    lines: List[Tuple[str, str]] = []
    for p in processes:
        m = result.metrics[p.pid]
        lines += [
            (f"{p.pid}   ·   AT={p.arrival}, BT={p.burst}", "head"),
            (f"  CT  = final CPU finish time = {m.completion}", "body"),
            (f"  TAT = CT - AT = {m.completion} - {p.arrival} = {m.turnaround}", "body"),
            (f"  WT  = TAT - BT = {m.turnaround} - {p.burst} = {m.waiting}", "body"),
            (f"  RT  = first start - AT = {m.first_start} - {p.arrival} = {m.response}",
             "body"),
            ("", "body"),
        ]
    n = len(result.metrics)
    for attr, label, code in (("turnaround", "Turnaround", "TAT"),
                              ("waiting", "Waiting", "WT"),
                              ("response", "Response", "RT")):
        values = [getattr(result.metrics[p.pid], attr) for p in processes]
        lines.append((f"Average {label} ({code}) = ({' + '.join(map(str, values))}) "
                      f"/ {n} = {sum(values) / n:.2f}", "avg"))
    s = result.summary
    lines += [
        (f"CPU utilization = busy / makespan = {s.busy} / {s.makespan} = "
         f"{s.utilization:.1f}%", "avg"),
        (f"Throughput = processes / makespan = {n} / {s.makespan} = "
         f"{s.throughput:.3f} per time unit", "avg"),
        (f"Context switches = {s.context_switches}", "avg"),
    ]
    return lines


class AlgorithmTab:
    """One algorithm's tab: KPIs, Gantt chart, metrics table, live calculations."""

    KPI_DEFS = (("Avg TAT", "avg_tat"), ("Avg WT", "avg_wt"), ("Avg RT", "avg_rt"),
                ("CPU utilization", "utilization"), ("Throughput", "throughput"),
                ("Context switches", "context_switches"))

    def __init__(self, notebook: ttk.Notebook, spec: AlgoSpec,
                 color_for: Callable[[str], str]):
        self.spec = spec
        self.frame = ScrollFrame(notebook)
        body = self.frame.body
        self._calc_token = 0

        make_label(body, spec.heading, 16, TEXT, True).pack(
            anchor="w", padx=20, pady=(18, 0))
        make_label(body, spec.subtitle, 9, MUTED).pack(anchor="w", padx=20, pady=(2, 12))

        kpis = tk.Frame(body, bg=BG)
        kpis.pack(fill="x", padx=20, pady=(0, 14))
        self.kpis: Dict[str, KpiTile] = {}
        for col, (caption, attr) in enumerate(self.KPI_DEFS):
            tile = KpiTile(kpis, caption, ALGO_COLORS[spec.key])
            tile.grid(row=0, column=col, sticky="nsew", padx=(0 if col == 0 else 8, 0))
            kpis.columnconfigure(col, weight=1, uniform="kpi")
            self.kpis[attr] = tile

        head = section_header(body, "CPU EXECUTION TIMELINE", pady=(0, 7))
        FlatButton(head, "▶  Replay", self._replay, pad=(10, 4)).pack(side="right")
        self.gantt = GanttChart(body, color_for)
        self.gantt.pack(fill="x", padx=20, pady=(0, 14))

        head = section_header(body, "PROCESS METRICS", pady=(0, 7))
        make_label(head, "amber row = longest wait", 8, MUTED).pack(side="right")
        self.tree = make_tree(body, [("pid", "Process", 90), ("at", "AT", 70),
                                     ("bt", "BT", 70), ("ct", "CT", 70),
                                     ("tat", "TAT", 70), ("wt", "WT", 70),
                                     ("rt", "RT", 70)], height=5, stretch=True)
        self.tree.pack(fill="x", padx=20, pady=(0, 14))

        section_header(body, "LIVE CALCULATION BREAKDOWN", pady=(0, 7))
        self.calc = tk.Text(body, height=11, bg="#0D1828", fg="#D7E5F3",
                            insertbackground=TEXT, relief="flat", wrap="word",
                            padx=14, pady=10, font=mono(9), spacing1=2, spacing3=2,
                            highlightthickness=1, highlightbackground=BORDER)
        self.calc.tag_configure("head", foreground=ACCENT, font=(_MONO_FONT, 9, "bold"))
        self.calc.tag_configure("avg", foreground=ACCENT_2)
        self.calc.tag_configure("hint", foreground=MUTED)
        self.calc.pack(fill="x", padx=20, pady=(0, 14))

        self.log: Optional[ttk.Treeview] = None
        if spec.key == "RR":
            section_header(body, "QUANTUM EXECUTION LOG", pady=(0, 7))
            self.log = make_tree(body, [("n", "#", 50), ("pid", "Process", 110),
                                        ("slice", "CPU time slice", 150),
                                        ("ran", "Ran for", 90),
                                        ("rem", "Remaining burst", 130)],
                                 height=6, stretch=True)
            self.log.pack(fill="x", padx=20, pady=(0, 20))
        self.clear()

    def _replay(self) -> None:
        if self.gantt.timeline:
            self.gantt.replay()

    def clear(self) -> None:
        self._calc_token += 1
        self.gantt.clear()
        clear_tree(self.tree)
        for tile in self.kpis.values():
            tile.set("—")
        self._set_calc_text([("Run the simulation to see how CT, TAT, WT, RT and "
                              "the averages are calculated.", "hint")])
        if self.log:
            clear_tree(self.log)

    def _set_calc_text(self, lines: Sequence[Tuple[str, str]]) -> None:
        self.calc.config(state="normal")
        self.calc.delete("1.0", "end")
        for text, tag in lines:
            self.calc.insert("end", text + "\n", tag)
        self.calc.config(state="disabled")

    def show(self, result: Result, processes: Sequence[Process],
             animate: bool) -> None:
        s = result.summary
        formats = {"avg_tat": f"{s.avg_tat:.2f}", "avg_wt": f"{s.avg_wt:.2f}",
                   "avg_rt": f"{s.avg_rt:.2f}", "utilization": f"{s.utilization:.1f}%",
                   "throughput": f"{s.throughput:.3f}",
                   "context_switches": str(s.context_switches)}
        subs = {"avg_tat": "time units", "avg_wt": "time units",
                "avg_rt": "time units", "utilization": f"{s.busy} busy / {s.idle} idle",
                "throughput": "processes / unit", "context_switches": "process changes"}
        for attr, tile in self.kpis.items():
            tile.set(formats[attr], subs[attr])

        clear_tree(self.tree)
        worst = max((m.waiting for m in result.metrics.values()), default=0)
        for i, p in enumerate(processes):
            m = result.metrics[p.pid]
            tags = ["odd"] if i % 2 else []
            if worst > 0 and m.waiting == worst:
                tags.append("worst")
            self.tree.insert("", "end", tags=tags, values=(
                p.pid, m.arrival, m.burst, m.completion, m.turnaround,
                m.waiting, m.response))
        self.tree.configure(height=max(3, min(len(processes), 12)))

        if self.log:
            clear_tree(self.log)
            for n, (pid, start, end, rem) in enumerate(result.quantum_log, 1):
                self.log.insert("", "end", tags=["odd"] if n % 2 == 0 else [],
                                values=(n, pid, f"{start} – {end}", end - start, rem))
            self.log.configure(height=max(3, min(len(result.quantum_log), 10)))

        self.gantt.show(result.timeline, animate)
        self._reveal_calculations(build_calculation_lines(result, processes), animate)

    def _reveal_calculations(self, lines: Sequence[Tuple[str, str]],
                             animate: bool) -> None:
        self._calc_token += 1
        token = self._calc_token
        if not animate:
            self._set_calc_text(lines)
            return
        self._set_calc_text([])
        delay = max(12, min(95, int(1800 / max(len(lines), 1))))

        def reveal(index: int) -> None:
            if token != self._calc_token or index >= len(lines):
                return
            text, tag = lines[index]
            self.calc.config(state="normal")
            self.calc.insert("end", text + "\n", tag)
            self.calc.see("end")
            self.calc.config(state="disabled")
            self.calc.after(delay, lambda: reveal(index + 1))
        reveal(0)


def _winners(results: Sequence[Result], attr: str) -> Tuple[List[str], float]:
    """Algorithms with the lowest value of a Summary attribute (ties included)."""
    best = min(getattr(r.summary, attr) for r in results)
    return [r.key for r in results if abs(getattr(r.summary, attr) - best) < 1e-9], best


def build_insights(results: Sequence[Result]) -> List[str]:
    """Plain-language findings that react to the actual numbers."""
    lines = []
    for label, attr, unit in (("average waiting time", "avg_wt", "units"),
                              ("average turnaround time", "avg_tat", "units"),
                              ("average response time", "avg_rt", "units"),
                              ("worst single wait", "max_wt", "units"),
                              ("context switches", "context_switches", "")):
        names, best = _winners(results, attr)
        shown = f"{best:g}" if attr in ("max_wt", "context_switches") else f"{best:.2f}"
        verdict = "all tied" if len(names) == len(results) else " / ".join(names)
        lines.append(f"•  Lowest {label}: {verdict}  ({shown} {unit}".rstrip() + ")")
    utils = {round(r.summary.utilization, 6) for r in results}
    if len(utils) == 1:
        s = results[0].summary
        lines.append(f"•  CPU utilization is identical ({s.utilization:.1f}%) because "
                     "every algorithm here is work-conserving: it never idles while "
                     "a process is ready.")
    lines.append("")
    lines.append("FCFS is simple and fair by arrival, but one long job delays everyone "
                 "behind it. SJF usually lowers waiting time, yet long jobs can be "
                 "starved. SRTF reacts to newly arrived short jobs at the cost of more "
                 "context switches. Round Robin shares the CPU fairly and gives quick "
                 "first responses; how well it does depends strongly on the quantum.")
    return lines


class ComparisonTab:
    """Side-by-side comparison: winner tiles, table, switchable chart, insights."""

    CHARTS = ("Average times (TAT / WT / RT)", "Waiting time per process",
              "Turnaround time per process", "Response time per process")

    def __init__(self, notebook: ttk.Notebook):
        self.frame = ScrollFrame(notebook)
        body = self.frame.body
        self.results: List[Result] = []
        self.processes: List[Process] = []

        make_label(body, "At a glance", 16, TEXT, True).pack(
            anchor="w", padx=20, pady=(18, 0))
        make_label(body, "All four algorithms on the same workload · ★ marks the best "
                         "(lowest) value in each column", 9, MUTED).pack(
            anchor="w", padx=20, pady=(2, 12))

        tiles = tk.Frame(body, bg=BG)
        tiles.pack(fill="x", padx=20, pady=(0, 14))
        self.tiles: Dict[str, KpiTile] = {}
        for col, (caption, attr, color) in enumerate((
                ("Best avg turnaround", "avg_tat", METRIC_COLORS["TAT"]),
                ("Best avg waiting", "avg_wt", METRIC_COLORS["WT"]),
                ("Best avg response", "avg_rt", METRIC_COLORS["RT"]),
                ("Fewest context switches", "context_switches", ACCENT))):
            tile = KpiTile(tiles, caption, color)
            tile.grid(row=0, column=col, sticky="nsew", padx=(0 if col == 0 else 8, 0))
            tiles.columnconfigure(col, weight=1, uniform="win")
            self.tiles[attr] = tile

        self.tree = make_tree(body, [("alg", "Algorithm", 210), ("tat", "Avg TAT", 95),
                                     ("wt", "Avg WT", 95), ("rt", "Avg RT", 95),
                                     ("mwt", "Max WT", 95), ("cs", "Ctx switches", 105)],
                              height=4, stretch=True)
        self.tree.pack(fill="x", padx=20, pady=(0, 16))

        head = section_header(body, "CHARTS", pady=(0, 8))
        self.chart_choice = tk.StringVar(value=self.CHARTS[0])
        picker = ttk.Combobox(head, textvariable=self.chart_choice, values=self.CHARTS,
                              state="readonly", width=30)
        picker.pack(side="right")
        picker.bind("<<ComboboxSelected>>", lambda _e: self._update_chart(True))
        self.chart = BarChart(body, height=310)
        self.chart.pack(fill="x", padx=20, pady=(0, 16))

        section_header(body, "WHAT THE NUMBERS SAY", pady=(0, 7))
        self.insights = tk.Label(body, text="Run the simulation to see findings.",
                                 bg=PANEL, fg=MUTED, justify="left", anchor="nw",
                                 padx=16, pady=14, font=font(10), wraplength=700)
        self.insights.pack(fill="x", padx=20, pady=(0, 20))
        self.insights.bind("<Configure>", lambda e: self.insights.config(
            wraplength=max(300, e.width - 34)))

    def clear(self) -> None:
        self.results, self.processes = [], []
        clear_tree(self.tree)
        for tile in self.tiles.values():
            tile.set("—")
        self.chart.clear()
        self.insights.config(text="Run the simulation to see findings.", fg=MUTED)

    def show(self, results: Sequence[Result], processes: Sequence[Process],
             animate: bool) -> None:
        self.results, self.processes = list(results), list(processes)
        clear_tree(self.tree)
        best = {attr: min(getattr(r.summary, attr) for r in results)
                for attr in ("avg_tat", "avg_wt", "avg_rt", "max_wt", "context_switches")}

        def cell(r: Result, attr: str, fmt: str) -> str:
            value = getattr(r.summary, attr)
            star = "★ " if abs(value - best[attr]) < 1e-9 else ""
            return star + fmt.format(value)

        for i, r in enumerate(results):
            self.tree.insert("", "end", tags=["odd"] if i % 2 else [], values=(
                r.name, cell(r, "avg_tat", "{:.2f}"), cell(r, "avg_wt", "{:.2f}"),
                cell(r, "avg_rt", "{:.2f}"), cell(r, "max_wt", "{:d}"),
                cell(r, "context_switches", "{:d}")))

        for attr, tile in self.tiles.items():
            names, value = _winners(results, attr)
            shown = f"{value:g}" if attr == "context_switches" else f"{value:.2f}"
            tile.set("all tied" if len(names) == len(results) else " / ".join(names),
                     shown + ("" if attr == "context_switches" else " time units"))

        self._update_chart(animate)
        self.insights.config(text="\n".join(build_insights(results)), fg=TEXT)

    def _update_chart(self, animate: bool) -> None:
        if not self.results:
            return
        choice = self.chart_choice.get()
        if choice == self.CHARTS[0]:
            self.chart.set_data(
                [r.key for r in self.results],
                [("Avg TAT", METRIC_COLORS["TAT"], [r.summary.avg_tat for r in self.results]),
                 ("Avg WT", METRIC_COLORS["WT"], [r.summary.avg_wt for r in self.results]),
                 ("Avg RT", METRIC_COLORS["RT"], [r.summary.avg_rt for r in self.results])],
                fmt="{:.1f}", animate=animate)
            return
        attr = {self.CHARTS[1]: "waiting", self.CHARTS[2]: "turnaround",
                self.CHARTS[3]: "response"}[choice]
        self.chart.set_data(
            [p.pid for p in self.processes],
            [(r.key, ALGO_COLORS[r.key],
              [getattr(r.metrics[p.pid], attr) for p in self.processes])
             for r in self.results],
            fmt="{:.0f}", animate=animate)


# =============================================================================
# 8. APPLICATION
# =============================================================================

SAMPLE_WORKLOAD = [("P1", 0, 7), ("P2", 2, 4), ("P3", 4, 1), ("P4", 5, 4)]
DEFAULT_QUANTUM = 2


class SchedulerApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Schedulix: Interactive CPU Scheduling Simulator")
        self.root.withdraw()
        self._size_window()
        self.root.configure(bg=BG)

        self.settings = load_settings()
        self.processes: List[Process] = []
        self.results: List[Result] = []
        self.sound = SoundManager(bool(self.settings["sound"]))
        self.fullscreen = False
        self._colors: Dict[str, str] = {}
        self._history: List[List[Process]] = []
        self._future: List[List[Process]] = []

        self._style()
        self._build()
        self._bind_shortcuts()
        self._restore_workload()
        self.sound.start_music()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self._show_loading_screen()

    # -- window & style -----------------------------------------------------
    def _size_window(self) -> None:
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry(f"{min(1400, max(980, sw - 70))}x{min(920, max(650, sh - 90))}")
        self.root.minsize(min(1000, max(760, sw - 30)), min(650, max(560, sh - 40)))

    def _style(self) -> None:
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview", background=PANEL, foreground=TEXT,
                        fieldbackground=PANEL, rowheight=34, borderwidth=0,
                        font=font(10), relief="flat")
        style.configure("Treeview.Heading", background=PANEL_2, foreground=ACCENT,
                        relief="flat", borderwidth=0, padding=(10, 10),
                        font=font(9, True))
        style.map("Treeview", background=[("selected", "#245B60")],
                  foreground=[("selected", "#FFFFFF")])
        style.configure("TNotebook", background=BG, borderwidth=0,
                        tabmargins=(0, 0, 0, 0))
        style.configure("TNotebook.Tab", background=PANEL_2, foreground=MUTED,
                        padding=(18, 12), borderwidth=0, font=font(9, True))
        style.map("TNotebook.Tab", background=[("selected", ACCENT)],
                  foreground=[("selected", BG)])
        style.configure("TCombobox", fieldbackground=PANEL_2, background=PANEL_2,
                        foreground=TEXT, arrowcolor=ACCENT, bordercolor=BORDER,
                        lightcolor=PANEL_2, darkcolor=PANEL_2)
        style.map("TCombobox", fieldbackground=[("readonly", PANEL_2)],
                  foreground=[("readonly", TEXT)],
                  selectbackground=[("readonly", PANEL_2)],
                  selectforeground=[("readonly", TEXT)])
        self.root.option_add("*TCombobox*Listbox.background", PANEL_2)
        self.root.option_add("*TCombobox*Listbox.foreground", TEXT)
        self.root.option_add("*TCombobox*Listbox.selectBackground", "#245B60")
        for orient in ("Vertical", "Horizontal"):
            name = f"{orient}.TScrollbar"
            style.configure(name, background="#35536B", troughcolor="#101D2D",
                            bordercolor="#101D2D", lightcolor="#35536B",
                            darkcolor="#35536B", arrowcolor=MUTED, relief="flat",
                            borderwidth=0, arrowsize=12, width=12)
            style.map(name, background=[("pressed", ACCENT), ("active", "#55CDB8")])

    # -- splash screen ------------------------------------------------------
    def _show_loading_screen(self) -> None:
        """Animated splash shown before the workspace is revealed."""
        splash = tk.Toplevel(self.root)
        splash.overrideredirect(True)
        splash.configure(bg=BG)
        width, height = 760, 440
        x = (splash.winfo_screenwidth() - width) // 2
        y = (splash.winfo_screenheight() - height) // 2
        splash.geometry(f"{width}x{height}+{x}+{y}")
        splash.attributes("-topmost", True)

        cv = tk.Canvas(splash, width=width, height=height, bg=BG,
                       highlightthickness=1, highlightbackground=BORDER)
        cv.pack(fill="both", expand=True)
        cv.create_oval(520, -150, 900, 230, outline="#173B4A", width=2)
        cv.create_oval(555, -115, 865, 195, outline="#1B4B55", width=2)
        cv.create_oval(595, -75, 825, 155, outline="#245D61", width=2)
        cv.create_oval(645, -25, 775, 105, fill="#123B42", outline="")
        cv.create_text(58, 62, anchor="w", text="SCHEDULIX", fill=ACCENT,
                       font=font(10, True))
        cv.create_text(58, 145, anchor="w",
                       text="See how your CPU\nchooses what runs next.",
                       fill=TEXT, font=font(27, True), justify="left")
        cv.create_text(60, 235, anchor="w", text="Interactive CPU Scheduling Simulator",
                       fill=MUTED, font=font(11))
        cv.create_text(60, 315, anchor="w", text="INITIALIZING WORKSPACE",
                       fill=ACCENT, font=font(9, True))
        bx, by, bw, bh = 60, 340, 640, 7
        cv.create_rectangle(bx, by, bx + bw, by + bh, fill="#203149", outline="")
        bar = cv.create_rectangle(bx, by, bx, by + bh, fill=ACCENT, outline="")
        percent = cv.create_text(700, 365, anchor="e", text="0%", fill=MUTED,
                                 font=font(9))
        cv.create_text(60, 392, anchor="w",
                       text="FCFS   ·   SJF   ·   SRTF   ·   ROUND ROBIN",
                       fill="#647A91", font=font(9, True))

        state = {"value": 0}

        def finish() -> None:
            try:
                splash.destroy()
                self.root.deiconify()
                self.root.lift()
                self._on_ready()
            except tk.TclError:
                pass

        def animate() -> None:
            state["value"] = min(100, state["value"] + random.randint(4, 8))
            cv.coords(bar, bx, by, bx + bw * state["value"] / 100, by + bh)
            cv.itemconfigure(percent, text=f"{state['value']}%")
            splash.after(260 if state["value"] >= 100 else 65,
                         finish if state["value"] >= 100 else animate)

        splash.after(120, animate)

    # -- widget helpers -----------------------------------------------------
    def _button(self, parent: tk.Misc, text: str, command: Callable[[], None],
                kind: str = "secondary", **kw) -> FlatButton:
        def action() -> None:
            self.sound.click()
            command()
        return FlatButton(parent, text, action, kind, **kw)

    def _color(self, pid: str) -> str:
        return IDLE_COLOR if pid == IDLE else self._colors.get(pid, PALETTE[0])

    def _assign_colors(self) -> None:
        """Give every process a stable colour that survives removals and undo."""
        for p in self.processes:
            if p.pid not in self._colors:
                self._colors[p.pid] = PALETTE[len(self._colors) % len(PALETTE)]

    # -- layout -------------------------------------------------------------
    def _build(self) -> None:
        self._build_header()
        self._build_statusbar()          # packed first so it keeps the bottom edge
        body = tk.Frame(self.root, bg=BG)
        body.pack(fill="both", expand=True, padx=30, pady=(0, 10))
        self._build_sidebar(body)
        self._build_workspace(body)

    def _build_header(self) -> None:
        header = tk.Frame(self.root, bg=BG)
        header.pack(fill="x", padx=30, pady=(22, 16))
        brand = tk.Frame(header, bg=BG)
        brand.pack(side="left")
        make_label(brand, "WORKSPACE  /  OPERATING SYSTEMS", 8, ACCENT, True).pack(anchor="w")
        make_label(brand, "Schedulix", 27, TEXT, True).pack(anchor="w", pady=(4, 0))
        make_label(brand, "Interactive CPU Scheduling Simulator", 11, MUTED).pack(anchor="w")

        controls = tk.Frame(header, bg=BG)
        controls.pack(side="right", anchor="n")
        for text, command in (("Open", self.open_workload), ("Save", self.save_workload),
                              ("Export CSV", self.export_csv)):
            self._button(controls, text, command).pack(side="left", padx=(0, 8))
        self.sound_button = self._button(
            controls, "♫  Mute" if self.sound.enabled else "♫  Unmute", self._toggle_sound)
        self.sound_button.pack(side="left", padx=(8, 8))
        if not self.sound.available:
            self.sound_button.config(text="♫  Sound unavailable")
            self.sound_button.set_enabled(False)
        self.fullscreen_button = self._button(controls, "⛶  Full screen",
                                              self._toggle_fullscreen)
        self.fullscreen_button.pack(side="left")
        # Fullscreen hides the title bar, so offer a Quit button while it is active.
        self.quit_button = self._button(controls, "✕  Quit", self._on_close, "danger")

    def _build_statusbar(self) -> None:
        bar = tk.Frame(self.root, bg=PANEL, highlightthickness=1,
                       highlightbackground=BORDER)
        bar.pack(side="bottom", fill="x")
        self.status = make_label(bar, "Add processes, then run the simulation.", 9, MUTED)
        self.status.pack(side="left", padx=18, pady=7)
        make_label(bar, "Ctrl+R Run   ·   Ctrl+Z Undo   ·   Ctrl+1-5 Tabs   ·   Ctrl+S Save   ·   F11 Fullscreen",
                   8, "#647A91").pack(side="right", padx=18)

    def _build_sidebar(self, body: tk.Frame) -> None:
        shell = tk.Frame(body, bg=PANEL, width=335, highlightthickness=1,
                         highlightbackground=BORDER)
        shell.pack(side="left", fill="y", padx=(0, 16))
        shell.pack_propagate(False)
        scroll = ScrollFrame(shell, bg=PANEL)
        scroll.pack(fill="both", expand=True)
        side = scroll.body

        make_label(side, "01  /  PROCESS INPUT", 10, ACCENT, True).pack(
            anchor="w", padx=20, pady=(22, 14))

        form = tk.Frame(side, bg=PANEL)
        form.pack(fill="x", padx=18)
        for col, text in enumerate(("Process ID", "Arrival", "Burst")):
            make_label(form, text, 9, MUTED).grid(
                row=0, column=col, sticky="w", padx=(0 if col == 0 else 8, 0))
        self.pid_entry = make_entry(form, 7)
        self.at_entry = make_entry(form, 6)
        self.bt_entry = make_entry(form, 6)
        self.entries = {"pid": self.pid_entry, "arrival": self.at_entry,
                        "burst": self.bt_entry}
        for col, entry in enumerate((self.pid_entry, self.at_entry, self.bt_entry)):
            entry.grid(row=1, column=col, sticky="ew", ipady=3,
                       padx=(0 if col == 0 else 8, 0), pady=(5, 4))
            entry.bind("<Return>", lambda _e: self.add_process())
            entry.bind("<Key>", lambda _e: self._clear_form_error(), add="+")
        form.columnconfigure(0, weight=1)
        self.form_error = make_label(side, " ", 8, DANGER, wraplength=290, justify="left")
        self.form_error.pack(anchor="w", padx=18, pady=(0, 6))
        self._button(side, "＋  Add process", self.add_process, "primary").pack(
            fill="x", padx=18, pady=(0, 12))

        self.input_tree = make_tree(side, [("pid", "PID", 90), ("at", "AT", 80),
                                           ("bt", "BT", 80)], height=8, stretch=True)
        self.input_tree.pack(fill="x", padx=18)
        self.input_tree.bind("<<TreeviewSelect>>", self._on_row_select)
        self.input_tree.bind("<Delete>", lambda _e: self.remove_selected())
        make_label(side, "Select a row to edit it in the form above.", 8, MUTED).pack(
            anchor="w", padx=18, pady=(5, 8))

        row = tk.Frame(side, bg=PANEL)
        row.pack(fill="x", padx=18, pady=(0, 6))
        self.update_btn = self._button(row, "Update selected", self.update_selected,
                                       pad=(10, 8))
        self.update_btn.pack(side="left", expand=True, fill="x", padx=(0, 6))
        self.remove_btn = self._button(row, "Remove", self.remove_selected, "danger",
                                       pad=(10, 8))
        self.remove_btn.pack(side="left", expand=True, fill="x")
        row = tk.Frame(side, bg=PANEL)
        row.pack(fill="x", padx=18)
        self.undo_btn = self._button(row, "↶ Undo", self.undo, pad=(10, 8))
        self.undo_btn.pack(side="left", expand=True, fill="x", padx=(0, 6))
        self.redo_btn = self._button(row, "↷ Redo", self.redo, pad=(10, 8))
        self.redo_btn.pack(side="left", expand=True, fill="x", padx=(0, 6))
        self._button(row, "Clear all", self.clear_all, "danger", pad=(10, 8)).pack(
            side="left", expand=True, fill="x")

        make_label(side, "02  /  ROUND ROBIN QUANTUM", 10, ACCENT, True).pack(
            anchor="w", padx=20, pady=(26, 8))
        qrow = tk.Frame(side, bg=PANEL)
        qrow.pack(fill="x", padx=18)
        self.quantum_var = tk.StringVar(value=str(DEFAULT_QUANTUM))
        self.quantum_spin = tk.Spinbox(
            qrow, from_=1, to=MAX_QUANTUM, width=6, textvariable=self.quantum_var,
            bg="#0d171e", fg=TEXT, insertbackground=TEXT, relief="flat",
            buttonbackground=PANEL_2, font=font(10), highlightthickness=1,
            highlightbackground="#36505d", highlightcolor=ACCENT)
        self.quantum_spin.pack(side="left", ipady=3)
        make_label(qrow, "time units", 9, MUTED).pack(side="left", padx=8)
        self.quantum_var.trace_add("write", lambda *_: self._on_quantum_change())

        make_label(side, "03  /  OPTIONS", 10, ACCENT, True).pack(
            anchor="w", padx=20, pady=(26, 6))
        self.animate_var = tk.BooleanVar(value=bool(self.settings["animate"]))
        self.live_var = tk.BooleanVar(value=bool(self.settings["live"]))
        self.fullscreen_var = tk.BooleanVar(value=bool(self.settings["fullscreen"]))
        self.autorun_var = tk.BooleanVar(value=bool(self.settings["autorun"]))
        for text, var, hook in (
                ("Animate timeline & calculations", self.animate_var, None),
                ("Live update (re-run on every change)", self.live_var,
                 self._on_live_toggle),
                ("Start in full screen", self.fullscreen_var, None),
                ("Run automatically on startup", self.autorun_var, None)):
            tk.Checkbutton(side, text=text, variable=var, command=hook, bg=PANEL,
                           fg=TEXT, activebackground=PANEL, activeforeground=TEXT,
                           selectcolor=PANEL_2, highlightthickness=0, bd=0,
                           font=font(9), cursor="hand2", anchor="w").pack(
                fill="x", padx=16)

        self._button(side, "Run all algorithms", self.run_all, "primary").pack(
            fill="x", padx=18, pady=(22, 8))
        self._button(side, "🎲  Generate random processes",
                     self.generate_random).pack(fill="x", padx=18, pady=(0, 8))
        self._button(side, "Load sample data", self._load_sample).pack(
            fill="x", padx=18, pady=(0, 22))

    def _build_workspace(self, body: tk.Frame) -> None:
        right = tk.Frame(body, bg=BG)
        right.pack(side="left", fill="both", expand=True)
        top = tk.Frame(right, bg=BG)
        top.pack(fill="x")
        make_label(top, "04  /  SIMULATION WORKSPACE", 10, ACCENT, True).pack(side="left")
        self.stale_badge = make_label(top, "●  Results outdated, press Run (Ctrl+R)",
                                      9, ACCENT_2, True)

        self.tabs = ttk.Notebook(right)
        self.tabs.pack(fill="both", expand=True, pady=(14, 0))
        self.algo_tabs: Dict[str, AlgorithmTab] = {}
        for spec in ALGORITHMS:
            tab = AlgorithmTab(self.tabs, spec, self._color)
            self.tabs.add(tab.frame, text=spec.tab_title)
            self.algo_tabs[spec.key] = tab
        self.compare_tab = ComparisonTab(self.tabs)
        self.tabs.add(self.compare_tab.frame, text="COMPARISON")
        self.tabs.bind("<<NotebookTabChanged>>", self._on_tab_changed)

    def _on_tab_changed(self, _event=None) -> None:
        """Replay the Gantt animation each time an algorithm tab is opened."""
        if not (self.results and self.animate_var.get()):
            return
        index = self.tabs.index(self.tabs.select())
        if index < len(ALGORITHMS):
            self.algo_tabs[ALGORITHMS[index].key].gantt.replay()

    def _bind_shortcuts(self) -> None:
        for sequence, command in (
                ("<Control-r>", self.run_all), ("<Control-z>", self.undo),
                ("<Control-y>", self.redo), ("<Control-s>", self.save_workload),
                ("<Control-o>", self.open_workload),
                ("<F11>", self._toggle_fullscreen), ("<Escape>", self._exit_fullscreen)):
            self.root.bind(sequence, lambda _e, c=command: (c(), "break")[1])
        for number in range(1, 6):                       # Ctrl+1 .. Ctrl+5
            self.root.bind(f"<Control-Key-{number}>", lambda _e, i=number - 1: (
                self.tabs.select(i), "break")[1])

    # -- status helpers -----------------------------------------------------
    def _say(self, message: str, error: bool = False) -> None:
        self.status.config(text=message, fg=DANGER if error else MUTED)

    def _form_error(self, exc: ValidationError) -> None:
        self.form_error.config(text=exc.args[0])
        for name, entry in self.entries.items():
            mark_invalid(entry, name == exc.field)
        if exc.field in self.entries:
            self.entries[exc.field].focus_set()

    def _clear_form_error(self) -> None:
        self.form_error.config(text=" ")
        for entry in self.entries.values():
            mark_invalid(entry, False)

    def _set_stale(self, stale: bool) -> None:
        if stale:
            self.stale_badge.pack(side="right")
        else:
            self.stale_badge.pack_forget()

    # -- workload state (every change goes through _set_processes) -----------
    def _set_processes(self, new: Sequence[Process], *, record: bool = True,
                       status: Optional[str] = None) -> None:
        if record:
            self._history.append(self.processes)
            self._history = self._history[-100:]
            self._future.clear()
        self.processes = [replace(p, order=i) for i, p in enumerate(new)]
        self._assign_colors()
        self._refresh_input_tree()
        self._refresh_history_buttons()
        if status:
            self._say(status)
        self._workload_changed()

    def _workload_changed(self) -> None:
        """Results no longer match the inputs: clear, refresh or flag them."""
        if not self.processes:
            self._clear_results()
        elif self.live_var.get():
            self.run_all(live=True)
        elif self.results:
            self._set_stale(True)

    def _refresh_input_tree(self, keep: Optional[Sequence[str]] = None) -> None:
        clear_tree(self.input_tree)
        for i, p in enumerate(self.processes):
            self.input_tree.insert("", "end", iid=p.pid, tags=["odd"] if i % 2 else [],
                                   values=(p.pid, p.arrival, p.burst))
        if keep:
            present = [pid for pid in keep if self.input_tree.exists(pid)]
            if present:
                self.input_tree.selection_set(present)

    def _refresh_history_buttons(self) -> None:
        self.undo_btn.set_enabled(bool(self._history))
        self.redo_btn.set_enabled(bool(self._future))

    def _next_pid(self) -> str:
        used = {p.pid for p in self.processes}
        n = 1
        while f"P{n}" in used:
            n += 1
        return f"P{n}"

    def _reset_form(self) -> None:
        for entry, value in ((self.pid_entry, self._next_pid()),
                             (self.at_entry, "0"), (self.bt_entry, "5")):
            entry.delete(0, "end")
            entry.insert(0, value)
        self._clear_form_error()

    # -- editing actions ----------------------------------------------------
    def add_process(self) -> None:
        if len(self.processes) >= MAX_PROCESSES:
            self._form_error(ValidationError(
                "pid", f"You can add at most {MAX_PROCESSES} processes."))
            return
        try:
            pid, at, bt = validate_process(
                self.pid_entry.get(), self.at_entry.get(), self.bt_entry.get(),
                [p.pid for p in self.processes])
        except ValidationError as exc:
            self._form_error(exc)
            return
        self._set_processes(self.processes + [Process(pid, at, bt)],
                            status=f"Added {pid}.")
        self._reset_form()
        self.pid_entry.focus_set()
        self.pid_entry.selection_range(0, "end")

    def _on_row_select(self, _event=None) -> None:
        selected = self.input_tree.selection()
        if len(selected) != 1:
            return
        p = next((q for q in self.processes if q.pid == selected[0]), None)
        if p is None:
            return
        for entry, value in ((self.pid_entry, p.pid), (self.at_entry, p.arrival),
                             (self.bt_entry, p.burst)):
            entry.delete(0, "end")
            entry.insert(0, str(value))
        self._clear_form_error()

    def update_selected(self) -> None:
        selected = self.input_tree.selection()
        if len(selected) != 1:
            self._say("Select exactly one process row to update.", error=True)
            return
        old = selected[0]
        try:
            pid, at, bt = validate_process(
                self.pid_entry.get(), self.at_entry.get(), self.bt_entry.get(),
                [p.pid for p in self.processes if p.pid != old])
        except ValidationError as exc:
            self._form_error(exc)
            return
        self._set_processes(
            [Process(pid, at, bt) if p.pid == old else p for p in self.processes],
            status=f"Updated {pid}.")
        self.input_tree.selection_set(pid)

    def remove_selected(self) -> None:
        selected = set(self.input_tree.selection())
        if not selected:
            self._say("Select one or more rows to remove.", error=True)
            return
        self._set_processes([p for p in self.processes if p.pid not in selected],
                            status=f"Removed {', '.join(sorted(selected))}.")
        self._reset_form()

    def clear_all(self) -> None:
        if not self.processes:
            return
        self._set_processes([], status="Cleared all processes (Ctrl+Z to undo).")
        self._reset_form()

    def undo(self) -> None:
        if not self._history:
            return
        self._future.append(self.processes)
        self._set_processes(self._history.pop(), record=False, status="Undid last change.")

    def redo(self) -> None:
        if not self._future:
            return
        self._history.append(self.processes)
        self._set_processes(self._future.pop(), record=False, status="Redid change.")

    def _load_sample(self, record: bool = True) -> None:
        self.quantum_var.set(str(DEFAULT_QUANTUM))
        self._set_processes([Process(pid, at, bt) for pid, at, bt in SAMPLE_WORKLOAD],
                            record=record, status="Sample dataset loaded.")
        self._reset_form()

    def generate_random(self) -> None:
        count = random.randint(3, 6)
        new = [Process(f"P{i + 1}", random.randint(0, 8), random.randint(1, 10))
               for i in range(count)]
        self._set_processes(new, status=f"Generated {count} random processes. "
                                        "Press Run (Ctrl+R).")
        self._reset_form()

    # -- running ------------------------------------------------------------
    def _on_quantum_change(self) -> None:
        try:
            validate_quantum(self.quantum_var.get())
            mark_invalid(self.quantum_spin, False)
        except ValidationError:
            mark_invalid(self.quantum_spin, True)
            return
        if self.processes:
            self._workload_changed()

    def _on_live_toggle(self) -> None:
        if self.live_var.get() and self.processes:
            self.run_all(live=True)

    def run_all(self, live: bool = False) -> None:
        if not self.processes:
            self._say("Add at least one process before running.", error=True)
            return
        try:
            quantum = validate_quantum(self.quantum_var.get())
        except ValidationError as exc:
            mark_invalid(self.quantum_spin, True)
            self._say(str(exc), error=True)
            if self.results:
                self._set_stale(True)
            return
        animate = self.animate_var.get() and not live
        self.results = simulate(self.processes, quantum)
        for result in self.results:
            self.algo_tabs[result.key].show(result, self.processes, animate)
        self.compare_tab.show(self.results, self.processes, animate)
        self._set_stale(False)
        span = self.results[0].summary.makespan
        self._say(f"Simulation complete · {len(self.processes)} processes · "
                  f"makespan {span} · quantum {quantum}")

    def _clear_results(self) -> None:
        self.results = []
        for tab in self.algo_tabs.values():
            tab.clear()
        self.compare_tab.clear()
        self._set_stale(False)

    # -- files --------------------------------------------------------------
    def save_workload(self) -> None:
        if not self.processes:
            self._say("Nothing to save yet, add some processes first.", error=True)
            return
        try:
            quantum = validate_quantum(self.quantum_var.get())
        except ValidationError:
            quantum = DEFAULT_QUANTUM
        path = filedialog.asksaveasfilename(
            title="Save workload", defaultextension=".json",
            initialfile="workload.json", filetypes=[("Schedulix workload", "*.json")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(workload_to_dict(self.processes, quantum), handle, indent=2)
        except OSError as exc:
            messagebox.showerror("Could not save", str(exc))
            return
        self._say(f"Workload saved to {os.path.basename(path)}")

    def open_workload(self) -> None:
        path = filedialog.askopenfilename(
            title="Open workload", filetypes=[("Schedulix workload", "*.json"),
                                              ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as handle:
                processes, quantum = workload_from_dict(json.load(handle))
        except (OSError, ValueError) as exc:   # json errors are ValueErrors too
            messagebox.showerror("Could not open workload", str(exc))
            return
        self.quantum_var.set(str(quantum))
        self._set_processes(processes, status=f"Loaded {os.path.basename(path)} "
                                              f"({len(processes)} processes).")
        self._reset_form()

    def export_csv(self) -> None:
        if not self.results:
            self._say("Run the simulation first, then export the results.", error=True)
            return
        path = filedialog.asksaveasfilename(
            title="Export results", defaultextension=".csv",
            initialfile="schedulix_results.csv", filetypes=[("CSV file", "*.csv")])
        if not path:
            return
        try:
            export_results_csv(path, self.results, self.processes)
        except OSError as exc:
            messagebox.showerror("Could not export", str(exc))
            return
        self._say(f"Results exported to {os.path.basename(path)}")

    # -- window / sound -----------------------------------------------------
    def _set_fullscreen(self, on: bool) -> None:
        self.fullscreen = on
        try:
            self.root.attributes("-fullscreen", on)
        except tk.TclError:                      # platform without fullscreen support
            self.fullscreen = False
            return
        self.fullscreen_button.config(
            text="⛶  Exit full screen" if on else "⛶  Full screen")
        if on:
            self.quit_button.pack(side="left", padx=(8, 0))
        else:
            self.quit_button.pack_forget()

    def _toggle_fullscreen(self) -> None:
        self._set_fullscreen(not self.fullscreen)

    def _exit_fullscreen(self) -> None:
        if self.fullscreen:
            self._set_fullscreen(False)

    def _on_ready(self) -> None:
        """Called once the splash screen closes: apply startup preferences."""
        if self.fullscreen_var.get():
            self._set_fullscreen(True)
        if self.autorun_var.get() and self.processes:
            self.root.after(400, self.run_all)

    def _restore_workload(self) -> None:
        """Reopen the last session's workload, or fall back to the sample data."""
        saved = self.settings.get("workload")
        if saved:
            try:
                processes, quantum = workload_from_dict(saved)
            except ValueError:
                processes = None
            if processes:
                self.quantum_var.set(str(quantum))
                self._set_processes(processes, record=False,
                                    status="Restored your last workload.")
                self._reset_form()
                return
        self._load_sample(record=False)

    def _toggle_sound(self) -> None:
        self.sound_button.config(text="♫  Mute" if self.sound.toggle() else "♫  Unmute")

    def _on_close(self) -> None:
        try:
            quantum = validate_quantum(self.quantum_var.get())
        except ValidationError:
            quantum = DEFAULT_QUANTUM
        data = {"fullscreen": self.fullscreen_var.get(),
                "autorun": self.autorun_var.get(), "sound": self.sound.enabled,
                "animate": self.animate_var.get(), "live": self.live_var.get()}
        if self.processes:
            data["workload"] = workload_to_dict(self.processes, quantum)
        save_settings(data)
        self.sound.cleanup()
        self.root.destroy()


def main() -> None:
    root = tk.Tk()
    init_fonts(root)
    SchedulerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
