# Reproducibility — VRL experiments demo (inspect + diagnose + plan)

This demo extends the quick demo with:
- an inspect+diagnose phase that produces diagnostics JSON and a human-readable plan summary
- a planner simulator that produces a structured plan (JSON) and a textual summary
- aggregation that writes a simple metrics CSV based on diagnostics + plan

## Files added
- `experiments/scripts/inspect_and_diagnose.py`
- `experiments/scripts/planner_simulator.py`
- `experiments/scripts/make_sample_snapshots.py`
- `experiments/scripts/aggregate_results.py`
- example snapshots in `experiments/data/`

## Run locally
```bash
cd /path/to/VRL
git checkout experiments/setup
chmod +x experiments/run_demo.sh
./experiments/run_demo.sh
# results are in ./results/
cat results/demo_metrics.csv
cat results/plan_summary_1.txt
```

## CI
The CI job already runs `./experiments/run_demo.sh` and uploads the `results/` folder as an artifact.

## Notes
- Replace `planner_simulator.py` call with your real planner command and ensure it writes `plan.json` and a human-readable `plan_summary.txt` so aggregation continues to work.
- Add deterministic sample snapshots under `experiments/data/` to keep CI reproducible.
