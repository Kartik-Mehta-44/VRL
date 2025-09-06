#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
VENV_DIR="$REPO_ROOT/.venv_demo"
RESULTS_DIR="$REPO_ROOT/results"
PYTHON="$VENV_DIR/bin/python"

echo "=== VRL demo runner ==="
echo "Repo root: $REPO_ROOT"

# create results dir
mkdir -p "$RESULTS_DIR"

# create virtualenv if missing
if [ ! -x "$PYTHON" ]; then
  echo "Creating virtualenv at $VENV_DIR ..."
  python3 -m venv "$VENV_DIR"
  echo "Upgrading pip..."
  "$PYTHON" -m pip install --upgrade pip setuptools wheel >/dev/null
  if [ -f "$REPO_ROOT/requirements.txt" ]; then
    echo "Installing requirements.txt ..."
    "$PYTHON" -m pip install -r "$REPO_ROOT/requirements.txt"
  fi
  # Install minimal runtime deps used by the demo
  "$PYTHON" -m pip install --upgrade pip >/dev/null
  "$PYTHON" -m pip install python-dateutil >/dev/null
fi

echo "Running Python demo script..."
"$PYTHON" "$SCRIPT_DIR/scripts/run_demo.py" --output "$RESULTS_DIR/demo_metrics.csv" --quick

echo
echo "Demo completed. Results written to:"
echo "  $RESULTS_DIR/demo_metrics.csv"
ls -l "$RESULTS_DIR" || true
