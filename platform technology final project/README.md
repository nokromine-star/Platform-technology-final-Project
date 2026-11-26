# Schedulix: Interactive CPU Scheduling Simulator

Schedulix is a desktop app that shows how an operating system decides which process runs next. You enter a set of processes, and Schedulix runs the same workload through four classic CPU scheduling algorithms. It then lays the results side by side with Gantt charts, metric tables, step-by-step formulas and comparison charts.

It is written in Python with Tkinter and uses **only the standard library**, so there is nothing to install beyond Python itself.

> Built as a final project for an Operating Systems course.

---

## Algorithms

| Algorithm | Type | How it chooses the next process |
|---|---|---|
| **FCFS** (First Come, First Served) | Non-preemptive | Strictly by arrival time |
| **SJF** (Shortest Job First) | Non-preemptive | Shortest burst among the processes that have arrived; runs to completion |
| **SRTF** (Shortest Remaining Time First) | Preemptive | Least remaining work; a newly arrived shorter job takes the CPU |
| **Round Robin** | Preemptive | Fixed time quantum; processes take turns in a circular queue |

**Tie-breaking:** when two processes are equal, the one that arrived first runs first. If they also arrived together, the one entered first runs first.

**Round Robin convention:** processes that arrive *during* a time slice join the ready queue *before* the preempted process is placed back at the end.

---

## Features

### Simulation and visuals
- Animated **Gantt chart** per algorithm with a time axis, colour legend and hover tooltips (process, start, end, duration)
- **Replay** button, and the timeline replays automatically when you open a tab
- **Live calculation breakdown** that types out every formula (CT, TAT, WT, RT and the averages)
- **Round Robin quantum log** showing each slice and the burst remaining after it
- Per-process metric tables, with the longest wait highlighted in amber
- Splash screen, dark theme, and optional background music (Windows)

### Analytics
Each algorithm tab shows six stat cards:

- Average Turnaround Time (TAT)
- Average Waiting Time (WT)
- Average Response Time (RT)
- CPU utilization
- Throughput
- Context switches

The **Comparison** tab adds:

- A table with a ★ on the best value in each column
- Winner cards for turnaround, waiting, response and context switches
- An animated bar chart you can switch between average times and per-process waiting, turnaround or response
- A plain-language summary generated from your actual numbers

### Usability
- **Inline validation**: errors appear in red under the form instead of popups
- **Undo / Redo** for every change to the process list
- **Edit in place**: select a row, change the values, press *Update selected*
- **Save / Open** workloads as JSON
- **Export CSV** with metrics, summaries and the full Gantt timeline
- **Generate random processes** and **Load sample data**
- **Live update** option that re-runs everything on every change
- A "Results outdated" badge appears when inputs change after a run
- **Remembers your session**: settings and your last workload are restored on the next launch
- Optional **auto full screen** and **auto-run** on startup

---

## Requirements

- **Python 3.8 or newer**
- **Tkinter** (included with the standard Python installers for Windows and macOS)

On Linux, Tkinter is sometimes a separate package:

```bash
# Debian / Ubuntu
sudo apt install python3-tk
```

Background music and the click sound use `winsound`, so they work on **Windows only**. On other systems the app runs normally and the sound button is disabled.

---

## Running the app

```bash
python Schedulix-Interactive_CPU_Scheduling_Simulator.py
```

(Use `python3` on macOS and Linux.)

By default the app opens in full screen and runs the simulation automatically. Press **Esc** or **F11** to leave full screen, or use the **Quit** button in the header.

---

## How to use it

1. **Enter processes.** Type a Process ID, Arrival time and Burst time, then press **Add process** or hit **Enter**.
2. **Set the Round Robin quantum** (1 to 99 time units).
3. **Press Run all algorithms** (or `Ctrl+R`).
4. **Explore the tabs**: FCFS, SJF, SRTF, Round Robin, then **Comparison** to see them side by side.
5. **Experiment.** Change a process, undo it, or switch on *Live update* and watch the results change as you edit.

### Input rules

| Field | Rule |
|---|---|
| Process ID | 1 to 8 characters: letters, digits, `_` or `-`. Must be unique. `IDLE` is reserved. |
| Arrival | Whole number from 0 to 999 |
| Burst | Whole number from 1 to 999 |
| Quantum | Whole number from 1 to 99 |
| Processes | Up to 20 per workload |

---

## Metric definitions

| Metric | Formula |
|---|---|
| **CT** (Completion Time) | Time the process finishes its last burst |
| **TAT** (Turnaround Time) | `CT - AT` |
| **WT** (Waiting Time) | `TAT - BT` |
| **RT** (Response Time) | `first CPU start - AT` |
| **CPU utilization** | `busy time / makespan` |
| **Throughput** | `processes completed / makespan` |
| **Context switches** | Times the CPU is handed to a *different* process. Idle gaps are ignored, and a process that keeps running across merged slices is not a switch. |

*Makespan* is the time at which the last process finishes, measured from time 0.

### Example (built-in sample data)

Processes: P1 (AT 0, BT 7), P2 (AT 2, BT 4), P3 (AT 4, BT 1), P4 (AT 5, BT 4). Round Robin quantum: 2.

| Algorithm | Avg TAT | Avg WT | Avg RT | Context switches |
|---|---|---|---|---|
| FCFS | 8.75 | 4.75 | 4.75 | 3 |
| SJF | 8.00 | 4.00 | 4.00 | 3 |
| SRTF | **7.00** | **3.00** | **0.50** | 5 |
| Round Robin | 9.00 | 5.00 | 1.50 | 8 |

SRTF wins on every average here, but it also needs more context switches than FCFS or SJF. Round Robin's response time is far better than FCFS, which is exactly what time slicing is for.

---

## Keyboard shortcuts

| Shortcut | Action |
|---|---|
| `Enter` | Add process (when in the input form) |
| `Ctrl+R` | Run all algorithms |
| `Ctrl+Z` / `Ctrl+Y` | Undo / Redo |
| `Ctrl+S` / `Ctrl+O` | Save / Open workload |
| `Ctrl+1` to `Ctrl+5` | Switch tab |
| `Delete` | Remove selected process rows |
| `F11` | Toggle full screen |
| `Esc` | Leave full screen |

---

## Files the app reads and writes

### Workload file (`.json`)

Created by **Save**, read by **Open**:

```json
{
  "app": "Schedulix",
  "version": 1,
  "quantum": 2,
  "processes": [
    { "pid": "P1", "arrival": 0, "burst": 7 },
    { "pid": "P2", "arrival": 2, "burst": 4 }
  ]
}
```

Files are validated on load, so a malformed workload is rejected with a message instead of crashing the app.

### CSV export

**Export CSV** (available after a run) writes three tables to one file: per-process metrics for every algorithm, a summary table, and the full Gantt timeline.

### Saved preferences

The app stores your preferences and last workload in `.schedulix_settings.json` in your home folder. Delete that file to reset everything to the defaults.

---

## Project structure

Everything lives in a single file, organised into clearly labelled sections:

| Section | Contents |
|---|---|
| 1. Data models | `Process`, `Metrics`, `Summary`, `Result` |
| 2. Scheduling algorithms | `fcfs`, `sjf`, `srtf`, `round_robin`, `simulate`. Pure functions with no GUI code. |
| 3. Validation & storage | Input validation, JSON workloads, CSV export |
| 4. Sound | Generated background music and click sound |
| 5. Theme & widgets | Colours, fonts, `FlatButton`, `KpiTile`, `ScrollFrame` |
| 6. Charts | `GanttChart`, `BarChart` (drawn on Tk canvases) |
| 7. Result tabs | `AlgorithmTab`, `ComparisonTab` |
| 8. Application | `SchedulerApp`, which connects everything |

Because the algorithms are separate from the interface, they can be imported and tested without opening a window.

---

## Limitations

- All times are whole numbers (time units, not milliseconds).
- Context-switch overhead is not simulated; switching is instantaneous.
- Priority scheduling and multilevel queues are intentionally not included.
