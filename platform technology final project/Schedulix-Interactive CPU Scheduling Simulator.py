

from __future__ import annotations

import tkinter as tk
from tkinter import ttk, messagebox
from dataclasses import dataclass
from typing import List, Dict, Tuple
import math
import os
import struct
import tempfile
import wave
import random


# Scheduling logic

@dataclass
class Process:
    pid: str
    arrival: int
    burst: int
    order: int


@dataclass
class Result:
    name: str
    timeline: List[Tuple[str, int, int]]
    metrics: Dict[str, Dict[str, int]]
    quantum_log: List[Tuple[str, int, int, int]]


def _metrics(processes, timeline):
    data = {}
    for p in processes:
        runs = [(s, e) for pid, s, e in timeline if pid == p.pid]
        if not runs:
            continue
        first_start = min(s for s, _ in runs)
        completion = max(e for _, e in runs)
        turnaround = completion - p.arrival
        waiting = turnaround - p.burst
        response = first_start - p.arrival
        data[p.pid] = {
            "AT": p.arrival, "BT": p.burst, "CT": completion,
            "TAT": turnaround, "WT": waiting, "RT": response
        }
    return data


def _append_segment(timeline, pid, start, end):
    if end <= start:
        return
    if timeline and timeline[-1][0] == pid and timeline[-1][2] == start:
        old_pid, old_start, _ = timeline[-1]
        timeline[-1] = (old_pid, old_start, end)
    else:
        timeline.append((pid, start, end))


def fcfs(processes):
    ordered = sorted(processes, key=lambda p: (p.arrival, p.order))
    t, timeline = 0, []
    for p in ordered:
        if t < p.arrival:
            _append_segment(timeline, "IDLE", t, p.arrival)
            t = p.arrival
        _append_segment(timeline, p.pid, t, t + p.burst)
        t += p.burst
    return Result("FCFS", timeline, _metrics(processes, timeline), [])


def sjf(processes):
    t, done, timeline = 0, set(), []
    while len(done) < len(processes):
        ready = [p for p in processes if p.pid not in done and p.arrival <= t]
        if not ready:
            next_time = min(p.arrival for p in processes if p.pid not in done)
            _append_segment(timeline, "IDLE", t, next_time)
            t = next_time
            continue
        p = min(ready, key=lambda x: (x.burst, x.arrival, x.order))
        _append_segment(timeline, p.pid, t, t + p.burst)
        t += p.burst
        done.add(p.pid)
    return Result("SJF (Non-preemptive)", timeline, _metrics(processes, timeline), [])


def srtf(processes):
    remaining = {p.pid: p.burst for p in processes}
    by_id = {p.pid: p for p in processes}
    completed, timeline, t = set(), [], 0
    while len(completed) < len(processes):
        ready = [p for p in processes
                 if p.pid not in completed and p.arrival <= t and remaining[p.pid] > 0]
        if not ready:
            next_time = min(p.arrival for p in processes if p.pid not in completed)
            _append_segment(timeline, "IDLE", t, next_time)
            t = next_time
            continue
        p = min(ready, key=lambda x: (remaining[x.pid], x.arrival, x.order))
        _append_segment(timeline, p.pid, t, t + 1)
        remaining[p.pid] -= 1
        t += 1
        if remaining[p.pid] == 0:
            completed.add(p.pid)
    return Result("SRTF (Preemptive)", timeline, _metrics(processes, timeline), [])


def round_robin(processes, quantum):
    remaining = {p.pid: p.burst for p in processes}
    timeline, log = [], []
    ordered = sorted(processes, key=lambda p: (p.arrival, p.order))
    ready, added, completed = [], set(), set()
    t, index = 0, 0

    while len(completed) < len(processes):
        while index < len(ordered) and ordered[index].arrival <= t:
            ready.append(ordered[index])
            index += 1

        if not ready:
            if index < len(ordered):
                next_time = ordered[index].arrival
                _append_segment(timeline, "IDLE", t, next_time)
                t = next_time
                continue
            break

        p = ready.pop(0)
        run_for = min(quantum, remaining[p.pid])
        start = t
        end = t + run_for
        _append_segment(timeline, p.pid, start, end)
        t = end
        remaining[p.pid] -= run_for

        # New arrivals during this time slice enter the queue before this
        # process is re-queued, which is the usual RR ready-queue convention.
        while index < len(ordered) and ordered[index].arrival <= t:
            ready.append(ordered[index])
            index += 1

        log.append((p.pid, start, end, remaining[p.pid]))
        if remaining[p.pid] == 0:
            completed.add(p.pid)
        else:
            ready.append(p)

    return Result("Round Robin", timeline, _metrics(processes, timeline), log)


# Interface 

BG = "#080F1C"          # deep midnight
PANEL = "#111D2E"       # raised surface
PANEL_2 = "#1A2A40"     # controls / secondary surface
TEXT = "#F3F7FC"
MUTED = "#91A3B8"
ACCENT = "#48E0C0"
ACCENT_2 = "#FFBE6B"
BORDER = "#263A52"
COLORS = ["#63d6bd", "#7ca9f5", "#f3b562", "#d69bea",
          "#f28f8f", "#91c98b", "#e6a66b", "#8bc7d9"]


class SchedulerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Schedulix: Interactive CPU Scheduling Simulator")
        self.root.withdraw()
        # Fit the available desktop instead of assuming a large monitor.
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        start_w = min(1380, max(980, screen_w - 70))
        start_h = min(900, max(650, screen_h - 90))
        self.root.geometry(f"{start_w}x{start_h}")
        self.root.minsize(min(1000, max(760, screen_w - 30)),
                          min(650, max(560, screen_h - 40)))
        self.root.configure(bg=BG)
        self.processes = []
        self.results = []
        self._animation_jobs = {}
        self._animation_tokens = {}
        self.fullscreen = False
        self.music_muted = False
        self.music_file = None
        self._style()
        self._build()
        self._load_sample()
        self._prepare_music()
        self._start_music()
        self.root.bind("<F11>", self._toggle_fullscreen)
        self.root.bind("<Escape>", self._exit_fullscreen)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self._show_loading_screen()

    def _style(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview", background=PANEL, foreground=TEXT,
                        fieldbackground=PANEL, rowheight=36, borderwidth=0,
                        font=("Segoe UI", 10), relief="flat")
        style.configure("Treeview.Heading", background=PANEL_2,
                        foreground=ACCENT, relief="flat", borderwidth=0,
                        padding=(10, 11), font=("Segoe UI", 9, "bold"))
        style.map("Treeview", background=[("selected", "#245B60")],
                  foreground=[("selected", "#FFFFFF")])
        style.configure("TNotebook", background=BG, borderwidth=0, tabmargins=(0, 0, 0, 0))
        style.configure("TNotebook.Tab", background=PANEL_2, foreground=MUTED,
                        padding=(18, 12), borderwidth=0,
                        font=("Segoe UI", 9, "bold"))
        style.map("TNotebook.Tab", background=[("selected", ACCENT)],
                  foreground=[("selected", BG)], padding=[("selected", (18, 12))])
        style.configure("TCombobox", fieldbackground=PANEL, background=PANEL_2,
                        foreground=TEXT, arrowcolor=ACCENT)

        # Visible modern scrollbars: keep a clear thumb and track.
        # A slightly wider thumb is easier to find and drag than a hairline.
        for orient in ("Vertical", "Horizontal"):
            style.configure(
                f"{orient}.TScrollbar",
                background="#35536B",
                troughcolor="#101D2D",
                bordercolor="#101D2D",
                lightcolor="#35536B",
                darkcolor="#35536B",
                arrowcolor="#91A3B8",
                relief="flat",
                borderwidth=0,
                arrowsize=12,
                width=12,
            )
            style.map(
                f"{orient}.TScrollbar",
                background=[
                    ("pressed", "#48E0C0"),
                    ("active", "#55CDB8"),
                    ("!disabled", "#35536B"),
                ],
                troughcolor=[("!disabled", "#101D2D")],
            )

    def _show_loading_screen(self):
        """Display a polished animated splash screen before revealing the workspace."""
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
        # Decorative orbital rings and accent glow.
        cv.create_oval(520, -150, 900, 230, outline="#173B4A", width=2)
        cv.create_oval(555, -115, 865, 195, outline="#1B4B55", width=2)
        cv.create_oval(595, -75, 825, 155, outline="#245D61", width=2)
        cv.create_oval(645, -25, 775, 105, fill="#123B42", outline="")
        cv.create_text(58, 62, anchor="w", text="SCHEDULIX",
                       fill=ACCENT, font=("Segoe UI", 10, "bold"))
        cv.create_text(58, 145, anchor="w", text="See how your CPU\nchooses what runs next.",
                       fill=TEXT, font=("Segoe UI", 27, "bold"), justify="left")
        cv.create_text(60, 235, anchor="w", text="Interactive CPU Scheduling Simulator",
                       fill=MUTED, font=("Segoe UI", 11))
        cv.create_text(60, 315, anchor="w", text="INITIALIZING WORKSPACE",
                       fill=ACCENT, font=("Segoe UI", 9, "bold"))
        bar_x, bar_y, bar_w, bar_h = 60, 340, 640, 7
        cv.create_rectangle(bar_x, bar_y, bar_x + bar_w, bar_y + bar_h,
                            fill="#203149", outline="")
        progress = cv.create_rectangle(bar_x, bar_y, bar_x, bar_y + bar_h,
                                       fill=ACCENT, outline="")
        percent = cv.create_text(700, 365, anchor="e", text="0%",
                                 fill=MUTED, font=("Segoe UI", 9))
        cv.create_text(60, 392, anchor="w", text="FCFS   ·   SJF   ·   SRTF   ·   ROUND ROBIN",
                       fill="#647A91", font=("Segoe UI", 9, "bold"))

        state = {"value": 0}
        def animate():
            state["value"] += random.randint(4, 8)
            value = min(state["value"], 100)
            cv.coords(progress, bar_x, bar_y, bar_x + bar_w * value / 100, bar_y + bar_h)
            cv.itemconfigure(percent, text=f"{value}%")
            if value >= 100:
                splash.after(260, finish)
            else:
                splash.after(65, animate)

        def finish():
            try:
                splash.destroy()
                self.root.deiconify()
                self.root.lift()
            except tk.TclError:
                pass
        splash.after(120, animate)

    def _label(self, parent, text, size=10, color=TEXT, bold=False):
        return tk.Label(parent, text=text, bg=parent.cget("bg"), fg=color,
                        font=("Segoe UI Semibold" if bold else "Segoe UI", size))

    def _entry(self, parent, width=10):
        return tk.Entry(parent, width=width, bg="#0d171e", fg=TEXT,
                        insertbackground=TEXT, relief="flat",
                        highlightthickness=1, highlightbackground="#36505d",
                        highlightcolor=ACCENT, font=("Segoe UI", 10))

    def _click_sound(self):
        """Play a short UI click sound without requiring an audio package."""
        try:
            import winsound  # Standard library on Windows.
            winsound.Beep(850, 28)
        except (ImportError, RuntimeError):
            try:
                self.root.bell()
            except tk.TclError:
                pass

    def _button(self, parent, text, command, primary=False):
        def click_action():
            self._click_sound()
            command()

        return tk.Button(parent, text=text, command=click_action,
                         bg=ACCENT if primary else PANEL_2,
                         fg=BG if primary else TEXT,
                         activebackground="#8BEED8" if primary else "#29415D",
                         activeforeground=BG if primary else TEXT,
                         relief="flat", bd=0, padx=16, pady=11,
                         cursor="hand2", font=("Segoe UI", 9, "bold"),
                         highlightthickness=1,
                         highlightbackground=ACCENT if primary else BORDER)

    def _build(self):
        header = tk.Frame(self.root, bg=BG)
        header.pack(fill="x", padx=30, pady=(24, 18))
        brand = tk.Frame(header, bg=BG)
        brand.pack(side="left", fill="x", expand=True)
        self._label(brand, "WORKSPACE  /  OPERATING SYSTEMS", 8, ACCENT, True).pack(anchor="w")
        self._label(brand, "Schedulix", 27, TEXT, True).pack(anchor="w", pady=(5, 1))
        self._label(brand, "Interactive CPU Scheduling Simulator",
                    11, MUTED).pack(anchor="w")
        controls = tk.Frame(header, bg=BG)
        controls.place(relx=1.0, rely=0.25, anchor="ne")
        self.music_button = self._button(controls, "♫  Mute music", self._toggle_music)
        self.music_button.pack(side="left", padx=(0, 8))
        self.fullscreen_button = self._button(controls, "⛶  Full screen (F11)", self._toggle_fullscreen)
        self.fullscreen_button.pack(side="left")

        body = tk.Frame(self.root, bg=BG)
        body.pack(fill="both", expand=True, padx=30, pady=(0, 24))

        # Scrollable input sidebar: controls never disappear below the window
        # edge on shorter displays or when Windows display scaling is enabled.
        left_shell = tk.Frame(body, bg=PANEL, width=320,
                              highlightthickness=1, highlightbackground=BORDER)
        left_shell.pack(side="left", fill="y", padx=(0, 16))
        left_shell.pack_propagate(False)
        sidebar_canvas = tk.Canvas(left_shell, bg=PANEL, highlightthickness=0,
                                   bd=0, width=318)
        sidebar_scroll = ttk.Scrollbar(left_shell, orient="vertical",
                                       command=sidebar_canvas.yview)
        sidebar_canvas.configure(yscrollcommand=sidebar_scroll.set)
        sidebar_scroll.pack(side="right", fill="y")
        sidebar_canvas.pack(side="left", fill="both", expand=True)
        left = tk.Frame(sidebar_canvas, bg=PANEL, width=300)
        sidebar_window = sidebar_canvas.create_window((0, 0), window=left, anchor="nw")
        left.bind("<Configure>", lambda _e: sidebar_canvas.configure(
            scrollregion=sidebar_canvas.bbox("all")))
        sidebar_canvas.bind("<Configure>", lambda e: sidebar_canvas.itemconfigure(
            sidebar_window, width=e.width))
        def _sidebar_wheel(event):
            sidebar_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        sidebar_canvas.bind("<MouseWheel>", _sidebar_wheel)
        sidebar_canvas.bind("<Button-4>", lambda _e: sidebar_canvas.yview_scroll(-1, "units"))
        sidebar_canvas.bind("<Button-5>", lambda _e: sidebar_canvas.yview_scroll(1, "units"))
        self._label(left, "01  /  PROCESS INPUT", 10, ACCENT, True).pack(anchor="w", padx=20, pady=(22, 16))

        form = tk.Frame(left, bg=PANEL)
        form.pack(fill="x", padx=18)
        self._label(form, "Process ID", 9, MUTED).grid(row=0, column=0, sticky="w")
        self._label(form, "Arrival", 9, MUTED).grid(row=0, column=1, sticky="w", padx=(8, 0))
        self._label(form, "Burst", 9, MUTED).grid(row=0, column=2, sticky="w", padx=(8, 0))
        self.pid_entry = self._entry(form, 7)
        self.at_entry = self._entry(form, 6)
        self.bt_entry = self._entry(form, 6)
        self.pid_entry.grid(row=1, column=0, pady=(5, 10), sticky="ew")
        self.at_entry.grid(row=1, column=1, padx=(8, 0), pady=(5, 10))
        self.bt_entry.grid(row=1, column=2, padx=(8, 0), pady=(5, 10))
        self.pid_entry.insert(0, "P1")
        self.at_entry.insert(0, "0")
        self.bt_entry.insert(0, "5")
        self._button(form, "＋  Add process", self.add_process, True).grid(
            row=2, column=0, columnspan=3, sticky="ew", pady=(2, 12))

        self.input_tree = ttk.Treeview(left, columns=("pid", "at", "bt"),
                                       show="headings", height=8)
        for col, title, width in [("pid", "PID", 75), ("at", "AT", 65), ("bt", "BT", 65)]:
            self.input_tree.heading(col, text=title)
            self.input_tree.column(col, width=width, anchor="center")
        self.input_tree.pack(fill="x", padx=18)
        actions = tk.Frame(left, bg=PANEL)
        actions.pack(fill="x", padx=18, pady=10)
        self._button(actions, "Remove selected", self.remove_process).pack(side="left")
        self._button(actions, "Clear all", self.clear_processes).pack(side="right")

        self._label(left, "ROUND ROBIN QUANTUM", 9, MUTED, True).pack(
            anchor="w", padx=18, pady=(18, 5))
        qrow = tk.Frame(left, bg=PANEL)
        qrow.pack(fill="x", padx=18)
        self.quantum_entry = self._entry(qrow, 8)
        self.quantum_entry.insert(0, "2")
        self.quantum_entry.pack(side="left")
        self._label(qrow, "time units", 9, MUTED).pack(side="left", padx=8)
        self._button(left, "Run all algorithms", self.run_all, True).pack(
            fill="x", padx=18, pady=(22, 8))
        self._button(left, "🎲  Generate random processes", self.generate_random_processes).pack(
            fill="x", padx=18, pady=(0, 8))
        self._button(left, "Load sample data", self._load_sample).pack(
            fill="x", padx=18)

        right = tk.Frame(body, bg=BG)
        right.pack(side="left", fill="both", expand=True)
        top = tk.Frame(right, bg=BG)
        top.pack(fill="x")
        self._label(top, "02  /  SIMULATION WORKSPACE", 10, ACCENT, True).pack(side="left")
        self.status = self._label(top, "Add processes, then run the simulation.", 9, MUTED)
        self.status.pack(side="right")

        self.tabs = ttk.Notebook(right)
        self.tabs.pack(fill="both", expand=True, pady=(16, 0))
        self.tab_frames = {}
        for key, title in [("FCFS", "FCFS"), ("SJF", "SJF"), ("SRTF", "SRTF"),
                           ("RR", "ROUND ROBIN"), ("COMPARE", "COMPARISON")]:
            frame = tk.Frame(self.tabs, bg=BG)
            self.tabs.add(frame, text=title)
            self.tab_frames[key] = frame

        self._make_result_tab("FCFS", "First Come, First Served")
        self._make_result_tab("SJF", "Shortest Job First · Non-preemptive")
        self._make_result_tab("SRTF", "Shortest Remaining Time First · Preemptive")
        self._make_result_tab("RR", "Round Robin · time-sliced execution")
        self._make_comparison_tab()

    def _make_result_tab(self, key, heading):
        # Each algorithm tab has its own scrollable workspace. This prevents
        # the calculation panel (and RR log) from being clipped on short screens.
        tab = self.tab_frames[key]
        shell = tk.Frame(tab, bg=BG)
        shell.pack(fill="both", expand=True)

        content_canvas = tk.Canvas(shell, bg=BG, highlightthickness=0, bd=0)
        scrollbar = ttk.Scrollbar(shell, orient="vertical",
                                  command=content_canvas.yview)
        content_canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        content_canvas.pack(side="left", fill="both", expand=True)

        content = tk.Frame(content_canvas, bg=BG)
        window_id = content_canvas.create_window((0, 0), window=content, anchor="nw")

        def update_scroll_region(_event=None):
            content_canvas.configure(scrollregion=content_canvas.bbox("all"))

        def fit_content_width(event):
            content_canvas.itemconfigure(window_id, width=event.width)

        content.bind("<Configure>", update_scroll_region)
        content_canvas.bind("<Configure>", fit_content_width)
        content_canvas.bind("<MouseWheel>",
                            lambda event: content_canvas.yview_scroll(
                                int(-event.delta / 120), "units"))
        content_canvas.bind("<Button-4>",
                            lambda _event: content_canvas.yview_scroll(-1, "units"))
        content_canvas.bind("<Button-5>",
                            lambda _event: content_canvas.yview_scroll(1, "units"))

        self._label(content, heading, 16, TEXT, True).pack(
            anchor="w", padx=20, pady=(18, 5))
        self._label(content, "CPU EXECUTION TIMELINE", 8, MUTED, True).pack(
            anchor="w", padx=20)
        canvas = tk.Canvas(content, height=112, bg=PANEL, highlightthickness=0,
                           bd=0, relief="flat")
        canvas.pack(fill="x", padx=20, pady=(8, 14))
        setattr(self, f"{key.lower()}_canvas", canvas)

        self._label(content, "PROCESS METRICS", 9, ACCENT, True).pack(
            anchor="w", padx=20, pady=(0, 7))
        tree = ttk.Treeview(content,
                            columns=("pid", "at", "bt", "ct", "tat", "wt", "rt"),
                            show="headings", height=5)
        headings = [("pid", "Process"), ("at", "AT"), ("bt", "BT"),
                    ("ct", "CT"), ("tat", "TAT"), ("wt", "WT"), ("rt", "RT")]
        for col, title in headings:
            tree.heading(col, text=title)
            tree.column(col, width=72 if col == "pid" else 62, anchor="center")
        tree.pack(fill="x", padx=20, pady=(0, 2))
        setattr(self, f"{key.lower()}_tree", tree)

        avg = self._label(content,
                          "Average TAT: —     Average WT: —     Average RT: —",
                          9, ACCENT_2, True)
        avg.pack(anchor="w", padx=20, pady=(10, 8))
        setattr(self, f"{key.lower()}_avg", avg)

        calc_header = tk.Frame(content, bg=BG)
        calc_header.pack(fill="x", padx=20, pady=(5, 6))
        self._label(calc_header, "LIVE CALCULATION BREAKDOWN", 9,
                    ACCENT, True).pack(side="left")
        self._label(calc_header, "STEP-BY-STEP", 8, MUTED, True).pack(side="right")

        calc = tk.Text(content, height=7, bg="#0D1828", fg="#D7E5F3",
                       insertbackground=TEXT, relief="flat", wrap="word",
                       padx=14, pady=10, font=("Cascadia Code", 9),
                       spacing1=2, spacing3=2,
                       highlightthickness=1, highlightbackground=BORDER)
        calc.pack(fill="x", padx=20, pady=(0, 14))
        calc.insert("end",
                    "Run the simulation to see how CT, TAT, WT, RT and the "
                    "averages are calculated.")
        calc.config(state="disabled")
        setattr(self, f"{key.lower()}_calc", calc)

        if key == "RR":
            self._label(content, "QUANTUM EXECUTION LOG", 9, ACCENT, True).pack(
                anchor="w", padx=20, pady=(2, 6))
            log = ttk.Treeview(content,
                               columns=("pid", "slice", "remaining"),
                               show="headings", height=4)
            for col, title in [("pid", "Process"),
                               ("slice", "CPU time slice"),
                               ("remaining", "Remaining burst")]:
                log.heading(col, text=title)
                log.column(col, width=150, anchor="center")
            log.pack(fill="x", padx=20, pady=(0, 16))
            self.rr_log = log

    def _make_comparison_tab(self):
        frame = self.tab_frames["COMPARE"]
        self._label(frame, "At a glance", 14, TEXT, True).pack(anchor="w", padx=16, pady=(18, 5))
        self._label(frame, "Average times across all entered processes", 9, MUTED).pack(
            anchor="w", padx=16)
        self.compare_tree = ttk.Treeview(frame, columns=("alg", "tat", "wt", "rt"),
                                         show="headings", height=6)
        for col, title, width in [("alg", "Algorithm", 220), ("tat", "Avg TAT", 110),
                                  ("wt", "Avg WT", 110), ("rt", "Avg RT", 110)]:
            self.compare_tree.heading(col, text=title)
            self.compare_tree.column(col, width=width, anchor="center")
        self.compare_tree.pack(fill="x", padx=16, pady=12)
        self.comparison_text = tk.Label(
            frame, text="Run the simulation to see a short comparison.",
            bg=PANEL, fg=MUTED, justify="left", anchor="nw",
            padx=16, pady=14, wraplength=650, font=("Segoe UI", 10))
        self.comparison_text.pack(fill="both", expand=True, padx=16, pady=(0, 16))

    def add_process(self):
        pid = self.pid_entry.get().strip().upper()
        try:
            arrival = int(self.at_entry.get())
            burst = int(self.bt_entry.get())
            if not pid or any(p.pid == pid for p in self.processes):
                raise ValueError("Use a unique, non-empty process ID.")
            if arrival < 0 or burst <= 0:
                raise ValueError("Arrival must be 0 or greater; burst must be positive.")
        except ValueError as exc:
            messagebox.showerror("Invalid process", str(exc) or "Enter whole numbers for arrival and burst.")
            return
        self.processes.append(Process(pid, arrival, burst, len(self.processes)))
        self.input_tree.insert("", "end", iid=pid, values=(pid, arrival, burst))
        self.pid_entry.delete(0, "end")
        self.pid_entry.insert(0, f"P{len(self.processes) + 1}")
        self.at_entry.delete(0, "end")
        self.at_entry.insert(0, "0")
        self.bt_entry.delete(0, "end")
        self.bt_entry.insert(0, "5")

    def generate_random_processes(self):
        """Replace the input list with a small, reproducible-style random workload."""
        self.clear_processes()
        count = random.randint(3, 6)
        generated = []
        for i in range(count):
            pid = f"P{i + 1}"
            arrival = random.randint(0, 8)
            burst = random.randint(1, 10)
            generated.append(Process(pid, arrival, burst, i))
        generated.sort(key=lambda p: (p.order, p.arrival))
        self.processes = generated
        for proc in generated:
            self.input_tree.insert("", "end", iid=proc.pid,
                                   values=(proc.pid, proc.arrival, proc.burst))
        self.status.config(text=f"Generated {count} random processes. Click Run all algorithms.")

    def remove_process(self):
        selected = self.input_tree.selection()
        if not selected:
            return
        ids = set(selected)
        self.processes = [p for p in self.processes if p.pid not in ids]
        for pid in selected:
            self.input_tree.delete(pid)
        self._renumber_order()

    def clear_processes(self):
        self.processes.clear()
        for item in self.input_tree.get_children():
            self.input_tree.delete(item)
        self._clear_results()

    def _renumber_order(self):
        self.processes.sort(key=lambda p: p.order)
        for i, p in enumerate(self.processes):
            p.order = i

    def _load_sample(self):
        self.clear_processes()
        sample = [("P1", 0, 7), ("P2", 2, 4), ("P3", 4, 1), ("P4", 5, 4)]
        for i, (pid, at, bt) in enumerate(sample):
            self.processes.append(Process(pid, at, bt, i))
            self.input_tree.insert("", "end", iid=pid, values=(pid, at, bt))
        self.quantum_entry.delete(0, "end")
        self.quantum_entry.insert(0, "2")
        self.status.config(text="Sample dataset loaded.")

    def run_all(self):
        if not self.processes:
            messagebox.showwarning("No processes", "Add at least one process before running.")
            return
        try:
            quantum = int(self.quantum_entry.get())
            if quantum <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Invalid quantum", "Round Robin quantum must be a positive whole number.")
            return

        self.results = [
            fcfs(self.processes), sjf(self.processes),
            srtf(self.processes), round_robin(self.processes, quantum)
        ]
        for key, result in zip(("FCFS", "SJF", "SRTF", "RR"), self.results):
            self._show_result(key, result)
        self._show_comparison()
        self.status.config(text=f"Simulation complete · {len(self.processes)} processes")

    def _show_result(self, key, result):
        tree = getattr(self, f"{key.lower()}_tree")
        for item in tree.get_children():
            tree.delete(item)
        for p in sorted(self.processes, key=lambda x: x.order):
            m = result.metrics[p.pid]
            tree.insert("", "end", values=(p.pid, m["AT"], m["BT"], m["CT"],
                                           m["TAT"], m["WT"], m["RT"]))
        count = len(result.metrics)
        avgs = {k: sum(m[k] for m in result.metrics.values()) / count
                for k in ("TAT", "WT", "RT")}
        getattr(self, f"{key.lower()}_avg").config(
            text=f"Average TAT: {avgs['TAT']:.2f}     "
                 f"Average WT: {avgs['WT']:.2f}     Average RT: {avgs['RT']:.2f}")
        self._draw_timeline(getattr(self, f"{key.lower()}_canvas"), result.timeline)
        self._animate_inline_calculations(key, result)
        if key == "RR":
            for item in self.rr_log.get_children():
                self.rr_log.delete(item)
            for pid, start, end, remaining in result.quantum_log:
                self.rr_log.insert("", "end",
                                   values=(pid, f"{start} – {end}", remaining))

    def _draw_timeline(self, canvas, timeline):
        # Animate blocks in sequence without blocking the Tkinter event loop.
        token = self._animation_tokens.get(canvas, 0) + 1
        self._animation_tokens[canvas] = token
        old_job = self._animation_jobs.get(canvas)
        if old_job is not None:
            try:
                self.root.after_cancel(old_job)
            except tk.TclError:
                pass
            self._animation_jobs.pop(canvas, None)
        canvas.delete("all")
        if not timeline:
            return
        width = max(canvas.winfo_width(), 620)
        left, right = 12, width - 12
        total = max(max(e for _, _, e in timeline), 1)
        usable = right - left
        y1, y2 = 24, 67
        def draw_one(i):
            if token != self._animation_tokens.get(canvas) or i >= len(timeline):
                return
            pid, start, end = timeline[i]
            x1 = left + usable * start / total
            x2 = left + usable * end / total
            if x2 - x1 < 1:
                x2 = x1 + 1
            color = "#52636b" if pid == "IDLE" else COLORS[
                next((j for j, p in enumerate(self.processes) if p.pid == pid), 0) % len(COLORS)]
            canvas.create_rectangle(x1, y1, x2, y2, fill=color, outline=BG, width=2)
            if x2 - x1 > 24:
                canvas.create_text((x1 + x2) / 2, (y1 + y2) / 2, text=pid,
                                   fill=BG, font=("Segoe UI Semibold", 9))
            canvas.create_text(x1, 82, text=str(start), fill=MUTED,
                               anchor="n", font=("Segoe UI", 8))
            if i == len(timeline) - 1:
                canvas.create_text(right, 82, text=str(end), fill=MUTED,
                                   anchor="n", font=("Segoe UI", 8))
            self._animation_jobs[canvas] = self.root.after(170, lambda: draw_one(i + 1))
        draw_one(0)

    def _animate_inline_calculations(self, key, result):
        """Reveal each process formula and the averages inside its own result tab."""
        widget = getattr(self, f"{key.lower()}_calc")
        lines = []
        ordered = sorted(self.processes, key=lambda proc: proc.order)
        for proc in ordered:
            metric = result.metrics[proc.pid]
            segments = [(a, b) for pid, a, b in result.timeline if pid == proc.pid]
            first_start = min(a for a, _ in segments)
            lines.extend([
                f"{proc.pid}: AT={proc.arrival}, BT={proc.burst}",
                f"  CT = final CPU finish time = {metric['CT']}",
                f"  TAT = CT - AT = {metric['CT']} - {proc.arrival} = {metric['TAT']}",
                f"  WT = TAT - BT = {metric['TAT']} - {proc.burst} = {metric['WT']}",
                f"  RT = first start - AT = {first_start} - {proc.arrival} = {metric['RT']}",
                "",
            ])
        n = len(result.metrics)
        for metric, label in (("TAT", "Turnaround"), ("WT", "Waiting"), ("RT", "Response")):
            values = [result.metrics[proc.pid][metric] for proc in ordered]
            total = sum(values)
            lines.append(f"Average {label} ({metric}) = ({' + '.join(map(str, values))}) / {n} = {total / n:.2f}")
        widget.config(state="normal")
        widget.delete("1.0", "end")
        widget.config(state="disabled")
        token = getattr(self, f"_{key.lower()}_calc_token", 0) + 1
        setattr(self, f"_{key.lower()}_calc_token", token)
        index = 0
        def reveal():
            nonlocal index
            if token != getattr(self, f"_{key.lower()}_calc_token", 0) or index >= len(lines):
                return
            widget.config(state="normal")
            widget.insert("end", lines[index] + "\n")
            widget.see("end")
            widget.config(state="disabled")
            index += 1
            self.root.after(95, reveal)
        reveal()

    def _toggle_fullscreen(self, event=None):
        self.fullscreen = not self.fullscreen
        self.root.attributes("-fullscreen", self.fullscreen)
        self.fullscreen_button.config(
            text="⛶  Exit full screen (Esc)" if self.fullscreen else "⛶  Full screen (F11)")
        return "break"

    def _exit_fullscreen(self, event=None):
        if self.fullscreen:
            self.fullscreen = False
            self.root.attributes("-fullscreen", False)
            self.fullscreen_button.config(text="⛶  Full screen (F11)")
        return "break"

    def _prepare_music(self):
        # Create a tiny looping instrumental WAV at runtime using only the standard library.
        try:
            sample_rate = 22050
            melody = [(261.63, .30), (329.63, .30), (392.00, .30), (329.63, .30),
                      (293.66, .30), (349.23, .30), (440.00, .30), (349.23, .30)]
            handle = tempfile.NamedTemporaryFile(prefix="cpu_lab_", suffix=".wav", delete=False)
            self.music_file = handle.name
            handle.close()
            with wave.open(self.music_file, "wb") as wav:
                wav.setnchannels(1)
                wav.setsampwidth(2)
                wav.setframerate(sample_rate)
                frames = bytearray()
                for frequency, duration in melody:
                    count = int(sample_rate * duration)
                    for n in range(count):
                        fade = min(1.0, n / 500, (count - n) / 500)
                        sample = int(1700 * fade * math.sin(2 * math.pi * frequency * n / sample_rate))
                        frames.extend(struct.pack("<h", sample))
                wav.writeframes(frames)
        except (OSError, wave.Error):
            self.music_file = None

    def _start_music(self):
        if self.music_muted or not self.music_file:
            return
        try:
            import winsound
            winsound.PlaySound(self.music_file, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_LOOP)
        except (ImportError, RuntimeError):
            self.music_button.config(text="♫  Music unavailable", state="disabled")

    def _toggle_music(self):
        try:
            import winsound
            if self.music_muted:
                self.music_muted = False
                self._start_music()
                self.music_button.config(text="♫  Mute music")
            else:
                winsound.PlaySound(None, winsound.SND_PURGE)
                self.music_muted = True
                self.music_button.config(text="♫  Unmute music")
        except (ImportError, RuntimeError):
            self.music_button.config(text="♫  Music unavailable", state="disabled")

    def _on_close(self):
        try:
            import winsound
            winsound.PlaySound(None, winsound.SND_PURGE)
        except (ImportError, RuntimeError):
            pass
        if self.music_file and os.path.exists(self.music_file):
            try:
                os.unlink(self.music_file)
            except OSError:
                pass
        self.root.destroy()

    def _show_comparison(self):
        for item in self.compare_tree.get_children():
            self.compare_tree.delete(item)
        rows = []
        for result in self.results:
            n = len(result.metrics)
            avg = {k: sum(m[k] for m in result.metrics.values()) / n
                   for k in ("TAT", "WT", "RT")}
            rows.append((result.name, avg))
            self.compare_tree.insert("", "end", values=(
                result.name, f"{avg['TAT']:.2f}", f"{avg['WT']:.2f}", f"{avg['RT']:.2f}"))
        best_wait = min(rows, key=lambda x: x[1]["WT"])
        best_turn = min(rows, key=lambda x: x[1]["TAT"])
        note = (
            f"Lowest average waiting time: {best_wait[0]} "
            f"({best_wait[1]['WT']:.2f} time units).\n\n"
            f"Lowest average turnaround time: {best_turn[0]} "
            f"({best_turn[1]['TAT']:.2f} time units).\n\n"
            "FCFS is simple and follows arrival order, but a long process can delay "
            "shorter ones. SJF often lowers waiting time when short jobs are ready, "
            "but long jobs may wait longer. SRTF can react to newly arrived short jobs, "
            "at the cost of more context switches. Round Robin shares CPU time fairly "
            "through fixed time slices; its behavior depends strongly on the quantum."
        )
        self.comparison_text.config(text=note)

    def _clear_results(self):
        for key in ("FCFS", "SJF", "SRTF", "RR"):
            tree = getattr(self, f"{key.lower()}_tree")
            for item in tree.get_children():
                tree.delete(item)
            getattr(self, f"{key.lower()}_canvas").delete("all")
            getattr(self, f"{key.lower()}_avg").config(
                text="Average TAT: —     Average WT: —     Average RT: —")
            calc = getattr(self, f"{key.lower()}_calc")
            calc.config(state="normal")
            calc.delete("1.0", "end")
            calc.insert("end", "Run the simulation to see the calculation breakdown.")
            calc.config(state="disabled")
        if hasattr(self, "rr_log"):
            for item in self.rr_log.get_children():
                self.rr_log.delete(item)
        if hasattr(self, "compare_tree"):
            for item in self.compare_tree.get_children():
                self.compare_tree.delete(item)
            self.comparison_text.config(text="Run the simulation to see a short comparison.")
        self.results = []


def main():
    root = tk.Tk()
    SchedulerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
