# experiments/

This folder will contain experiment scripts, datasets pointers, and small reproducible demos
for the VRL project.

## Suggested contents
- `run_demo.sh` — small executable that runs a quick demo/validation.
- `scripts/` — experiment runner scripts (python / rust wrappers).
- `data/` — small sample snapshots (gitignored).
- `results/` — output metrics saved as CSV/JSON (gitignored).

Keep this folder minimal and reproducible so GitHub Actions can run the demo.
