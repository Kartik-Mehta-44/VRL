# Reproducibility — VRL experiments demo

This document explains how to reproduce the quick demo locally and how CI runs it.

## Purpose
The demo is intentionally tiny: it creates a small JSON 'snapshot', performs a planner dry-run that
computes simple metrics, and writes those metrics to `results/demo_metrics.csv` so CI can collect them.

## Run locally (recommended)
1. Open a terminal and go to your local repo root (on branch `experiments/setup`):
   ```bash
   cd /path/to/VRL
   git checkout experiments/setup
   ```
2. Ensure the demo script is executable and run it:
   ```bash
   chmod +x experiments/run_demo.sh
   ./experiments/run_demo.sh
   ```
3. After completion, view results:
   ```bash
   cat results/demo_metrics.csv
   ```

## What the demo does
- Creates `data/sample_snapshot.json` — a simple snapshot with three entries (one 'bad' entry).
- Runs a small planner dry-run that counts files, sizes, and 'bad' entries.
- Writes `results/demo_metrics.csv` with simple `metric,value` rows.

## How CI runs the demo
The GitHub Actions workflow `.github/workflows/ci.yml` runs the demo in the `demo` job and uploads the entire `results/` folder as an artifact named `demo-results`.

## Expected output (example `results/demo_metrics.csv`)
```csv
metric,value
snapshot_id,demo-snap-001
total_files,3
total_size,384
bad_count,1
timestamp,2025-09-06T00:00:00Z
```

## Extending the demo
- Replace the simple planner dry-run with your real planner invocation (keep same --output CSV contract if possible).
- Add small, deterministic sample snapshots under `experiments/data/` for CI to use.
- Add unit tests for `experiments/scripts/run_demo.py` and include them in the `build-and-test` job.
