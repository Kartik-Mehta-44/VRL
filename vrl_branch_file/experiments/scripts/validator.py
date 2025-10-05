#!/usr/bin/env python3
"""
Validator (Python)

- Summarizes diagnostics JSON and/or runs a read-only e2fsck (-n) on an image.
- Produces validator JSON and optional human-readable summary.

Usage examples:
  # Validate diagnostics JSON
  python3 experiments/scripts/validator.py --diagnostics results/diagnostics_1.json --out results/validator_1.json --human results/validator_1.txt

  # Run read-only e2fsck on an image (requires sudo)
  sudo python3 experiments/scripts/validator.py --image experiments/data/corrupted.img --out results/validator_from_image.json --human results/validator_from_image.txt
"""
import argparse
import json
import os
import subprocess
from datetime import datetime

def run_e2fsck_readonly(img_path, timeout=300):
    """Run e2fsck -n on image and return (rc, stdout)."""
    cmd = ["sudo", "e2fsck", "-n", img_path]
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=timeout)
        return proc.returncode, proc.stdout
    except Exception as e:
        return -1, f"e2fsck invocation failed: {e}"

def summarize_diagnostics(diag_obj):
    d = diag_obj.get("diagnostics", diag_obj) if isinstance(diag_obj, dict) else diag_obj
    summary = {
        "snapshot_id": d.get("snapshot_id"),
        "total_files": d.get("total_files"),
        "total_size": d.get("total_size"),
        "duplicate_groups": len(d.get("duplicate_inodes", [])),
        "lost_found_entries": len(d.get("lost_found", [])),
        "zero_size_files": len(d.get("zero_size", []))
    }
    # heuristic verdict
    if summary["duplicate_groups"] == 0 and summary["lost_found_entries"] == 0:
        summary["verdict"] = "clean"
    else:
        summary["verdict"] = "needs_attention"
    return summary

def write_json(path, obj):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf8") as f:
        json.dump(obj, f, indent=2)

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--diagnostics", help="Diagnostics JSON (from inspect_and_diagnose.py)")
    p.add_argument("--image", help="Raw image file to run read-only e2fsck on (sudo may be required)")
    p.add_argument("--out", required=True, help="Output validator JSON")
    p.add_argument("--human", help="Optional human-readable summary text output")
    args = p.parse_args()

    result = {
        "generated_at": datetime.utcnow().isoformat() + "Z",
        "checked_image": os.path.abspath(args.image) if args.image else None,
        "checked_diagnostics": os.path.abspath(args.diagnostics) if args.diagnostics else None,
        "checks": {}
    }

    if args.diagnostics:
        try:
            with open(args.diagnostics, "r", encoding="utf8") as f:
                diag = json.load(f)
            result["checks"]["diagnostics_summary"] = summarize_diagnostics(diag)
        except Exception as e:
            result["checks"]["diagnostics_error"] = str(e)

    if args.image:
        rc, out = run_e2fsck_readonly(args.image)
        result["checks"]["e2fsck_rc"] = rc
        # store a short snippet
        result["checks"]["e2fsck_output_snippet"] = "\n".join((out or "").splitlines()[:400])
        # heuristic
        lowered = (out or "").lower()
        if "error" in lowered or "inode" in out or "unattached" in lowered or "corrupt" in lowered:
            result["checks"]["e2fsck_verdict_heuristic"] = "issues_found"
        else:
            result["checks"]["e2fsck_verdict_heuristic"] = "no_obvious_errors"

    write_json(args.out, result)

    if args.human:
        with open(args.human, "w", encoding="utf8") as fh:
            fh.write(f"Validator report — {result['generated_at']}\n")
            fh.write(f"Checked image: {result['checked_image']}\n")
            fh.write(f"Checked diagnostics: {result['checked_diagnostics']}\n\n")
            if "diagnostics_summary" in result["checks"]:
                ds = result["checks"]["diagnostics_summary"]
                fh.write("Diagnostics summary:\n")
                fh.write(f" - snapshot_id: {ds.get('snapshot_id')}\n")
                fh.write(f" - total_files: {ds.get('total_files')}\n")
                fh.write(f" - duplicate_groups: {ds.get('duplicate_groups')}\n")
                fh.write(f" - lost_found_entries: {ds.get('lost_found_entries')}\n")
                fh.write(f" - zero_size_files: {ds.get('zero_size_files')}\n")
                fh.write(f" - verdict: {ds.get('verdict')}\n\n")
            if "e2fsck_rc" in result["checks"]:
                fh.write("e2fsck (read-only) snippet:\n")
                fh.write(result["checks"]["e2fsck_output_snippet"] + "\n")
    print(f"Validator wrote {args.out}; verdict:",
          result["checks"].get("diagnostics_summary", {}).get("verdict", result["checks"].get("e2fsck_verdict_heuristic", "unknown")))

if __name__ == "__main__":
    main()
