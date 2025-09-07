#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
VENV_DIR="$REPO_ROOT/.venv_demo"
PYTHON="$VENV_DIR/bin/python"
RESULTS_DIR="$REPO_ROOT/results"

echo "=== VRL demo: inspect + diagnose + plan integration ==="
mkdir -p "$RESULTS_DIR"

# create virtualenv if missing
if [ ! -x "$PYTHON" ]; then
  echo "Creating virtualenv at $VENV_DIR ..."
  python3 -m venv "$VENV_DIR"
  "$PYTHON" -m pip install --upgrade pip setuptools wheel >/dev/null
  "$PYTHON" -m pip install python-dateutil >/dev/null
fi

# 1) run quick snapshot generator (if missing)
if [ ! -f experiments/data/sample_snapshot_1.json ]; then
  echo "Creating sample snapshot(s)..."
  "$PYTHON" experiments/scripts/make_sample_snapshots.py --out experiments/data
fi

# 2) run inspect+diagnose on the sample snapshot(s)
echo "Running inspect+diagnose..."
"$PYTHON" experiments/scripts/inspect_and_diagnose.py --snapshot experiments/data/sample_snapshot_1.json --out "$RESULTS_DIR/diagnostics_1.json" --summary "$RESULTS_DIR/plan_summary_1.txt"

# 3) Run the planner simulator to produce a plan JSON and human-readable summary
echo "Running planner simulator..."
"$PYTHON" experiments/scripts/planner_simulator.py --snapshot experiments/data/sample_snapshot_1.json --out-plan "$RESULTS_DIR/plan_1.json" --out-summary "$RESULTS_DIR/plan_summary_1.txt"

# 4) Integrate planner output into demo metrics (aggregated)
echo "Aggregating demo metrics..."
"$PYTHON" experiments/scripts/aggregate_results.py --diagnostics "$RESULTS_DIR/diagnostics_1.json" --plan "$RESULTS_DIR/plan_1.json" --out "$RESULTS_DIR/demo_metrics.csv"

echo "Demo artifacts written to $RESULTS_DIR:"
ls -l "$RESULTS_DIR" || true
echo "Preview plan summary:"
sed -n '1,200p' "$RESULTS_DIR/plan_summary_1.txt" || true

echo "Demo complete."
