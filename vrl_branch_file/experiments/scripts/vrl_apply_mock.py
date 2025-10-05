#!/usr/bin/env python3
"""
Mock VRL 'apply' for experiments.

Usage:
  python3 experiments/scripts/vrl_apply_mock.py --input corrupted.img --output repaired.img [--plan plan.json] [--sleep 1]

Behavior:
 - If --plan is provided, it prints the plan summary (first lines) to stdout.
 - Copies input -> output (simulates writing repaired image).
 - Writes a short validator-like JSON (repaired_metadata.json) in the same folder as output.
 - Returns exit code 0 on success, >0 on error.
"""
import argparse, shutil, os, json, time, sys
from datetime import datetime

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--input', required=True, help='Path to corrupted image')
    p.add_argument('--output', required=True, help='Path to write repaired image')
    p.add_argument('--plan', default=None, help='Optional plan JSON path (used for simulation)')
    p.add_argument('--sleep', type=float, default=0.5, help='Seconds to sleep to simulate work')
    p.add_argument('--verbose', action='store_true')
    args = p.parse_args()

    start = datetime.utcnow().isoformat() + "Z"
    print(f"[MOCK VRL] start: {start}")
    print(f"[MOCK VRL] input: {args.input}")
    print(f"[MOCK VRL] output: {args.output}")
    if args.plan:
        print(f"[MOCK VRL] using plan: {args.plan}")
        try:
            with open(args.plan, 'r', encoding='utf8') as f:
                plan = json.load(f)
            # print small summary of plan (first few actions)
            actions = plan.get('actions', []) if isinstance(plan, dict) else plan
            print(f"[MOCK VRL] plan_actions_count: {len(actions)}")
            for a in actions[:5]:
                print(f"  - {a}")
        except Exception as e:
            print(f"[MOCK VRL] failed to read plan: {e}", file=sys.stderr)

    # quick sanity checks
    if not os.path.exists(args.input):
        print(f"[MOCK VRL] ERROR: input file not found: {args.input}", file=sys.stderr)
        sys.exit(2)

    # simulate some processing time
    time.sleep(args.sleep)

    # copy input to output (simulating repair). create parent dir
    os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
    try:
        shutil.copy2(args.input, args.output)
    except Exception as e:
        print(f"[MOCK VRL] ERROR copying input->output: {e}", file=sys.stderr)
        sys.exit(3)

    # write a small validator JSON next to output to simulate validation result
    val = {
        "repaired_at": datetime.utcnow().isoformat() + "Z",
        "input": os.path.abspath(args.input),
        "output": os.path.abspath(args.output),
        "status": "simulated_repaired",
        "notes": "This is a mock VRL output for experiments. Replace with real VRL apply."
    }
    validator_path = os.path.splitext(os.path.abspath(args.output))[0] + "_validator.json"
    try:
        with open(validator_path, "w", encoding="utf8") as f:
            json.dump(val, f, indent=2)
    except Exception as e:
        print(f"[MOCK VRL] WARN: could not write validator json: {e}", file=sys.stderr)

    # print final summary and exit 0
    print(f"[MOCK VRL] wrote output: {args.output}")
    print(f"[MOCK VRL] validator: {validator_path}")
    print(f"[MOCK VRL] done.")
    sys.exit(0)

if __name__ == "__main__":
    main()
