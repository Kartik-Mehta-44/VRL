# Demo: inspect + diagnose + plan integration

This demo runs a small, deterministic pipeline:
1. create sample snapshot JSON(s)
2. inspect + diagnose the snapshot (produces diagnostics JSON and a human-readable plan summary)
3. run a planner simulator (produces plan.json and plan_summary.txt)
4. aggregate results into results/demo_metrics.csv

Files written to `results/`:
- diagnostics_1.json
- plan_1.json
- plan_summary_1.txt
- demo_metrics.csv

Replace the planner simulator with your real planner command if available.
