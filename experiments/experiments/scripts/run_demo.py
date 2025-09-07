#!/usr/bin/env python3
"""Simple demo script for VRL experiments
Creates a tiny sample snapshot JSON and runs a 'planner dry-run' producing a metrics CSV.
"""

import argparse, json, csv, os
from datetime import datetime


SAMPLE_SNAPSHOT = {
    "snapshot_id": "demo-snap-001",
    "created": None,
    "files": [
        {"path": "/file1.txt", "inode": 101, "size": 128, "bad": False},
        {"path": "/file2.txt", "inode": 102, "size": 256, "bad": False},
        {"path": "/lost+found/unknown", "inode": 103, "size": 0, "bad": True}
    ]
}


def make_snapshot(path):
    SAMPLE_SNAPSHOT["created"] = datetime.utcnow().isoformat() + "Z"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf8") as f:
        json.dump(SAMPLE_SNAPSHOT, f, indent=2)
    return path


def planner_dry_run(snapshot_path):
    # Very small 'planner' that checks for bad entries and computes simple metrics
    with open(snapshot_path, "r", encoding="utf8") as f:
        snap = json.load(f)
    files = snap.get("files", [])
    total_files = len(files)
    total_size = sum(f.get("size", 0) for f in files)
    bad_count = sum(1 for f in files if f.get("bad"))
    return {
        "snapshot_id": snap.get("snapshot_id"),
        "total_files": total_files,
        "total_size": total_size,
        "bad_count": bad_count,
        "timestamp": datetime.utcnow().isoformat() + "Z"
    }


def write_metrics_csv(metrics, out_path):
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", newline="", encoding="utf8") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["metric", "value"])
        for k, v in metrics.items():
            writer.writerow([k, v])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", "-o", required=True, help="CSV output path for metrics")
    parser.add_argument("--quick", action="store_true", help="Run the quick demo (default)")
    args = parser.parse_args()

    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    data_dir = os.path.join(repo_root, "data")
    snapshot_path = os.path.join(data_dir, "sample_snapshot.json")

    print("VRL demo: creating sample snapshot ->", snapshot_path)
    make_snapshot(snapshot_path)
    print("Snapshot created.")

    print("Running planner dry-run...")
    metrics = planner_dry_run(snapshot_path)
    print("Planner dry-run finished. Metrics:")
    for k, v in metrics.items():
        print(f"  {k}: {v}")

    print("Writing metrics to:", args.output)
    write_metrics_csv(metrics, args.output)
    print("Done.")

if __name__ == '__main__':
    main()
