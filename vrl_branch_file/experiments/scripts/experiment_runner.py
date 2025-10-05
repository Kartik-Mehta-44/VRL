#!/usr/bin/env python3
# experiments/scripts/experiment_runner.py
import argparse, os, shutil, subprocess, json, time
from datetime import datetime, timezone
from pathlib import Path

def run_cmd(cmd, cwd=None, timeout=None, capture=True):
    res = subprocess.run(cmd, cwd=cwd, shell=True, stdout=subprocess.PIPE if capture else None, stderr=subprocess.STDOUT if capture else None, timeout=timeout, text=True)
    return res.returncode, (res.stdout if capture else None)

def ensure_dir(path):
    os.makedirs(path, exist_ok=True)

def run_trial(base_img, trial_dir, trial_idx, duplicates, seed, vrl_cmd):
    ensure_dir(trial_dir)
    original = os.path.join(trial_dir, 'base_copy.img')
    shutil.copy2(base_img, original)
    corrupted = os.path.join(trial_dir, 'corrupted.img')

    # 1) seed duplicates
    pairs_json = os.path.join(trial_dir, 'pairs.json')
    cmd_seed = f'python3 experiments/scripts/seed_duplicate_blocks.py --input "{original}" --output "{corrupted}" --pairs {duplicates} --seed {seed} --pairs-json "{pairs_json}"'
    rc, out = run_cmd(cmd_seed)
    with open(os.path.join(trial_dir, 'seed.log'), 'w') as f: f.write(out or '')
    if rc != 0:
        return {'error': 'seed_failed', 'rc': rc, 'out': out}

    # 2) run e2fsck (baseline repair)
    e2fsck_log = os.path.join(trial_dir, 'e2fsck_fix.log')
    t0 = time.time()
    # -f force, -y assume yes to fixes, -v verbose
    rc, out = run_cmd(f'sudo e2fsck -fy "{corrupted}"', capture=True)
    dur = time.time() - t0
    with open(e2fsck_log, 'w') as f:
        f.write(out or '')
    # capture exit code and duration
    e2fsck_result = {'rc': rc, 'duration_s': dur, 'log': e2fsck_log}

    # 3) run VRL apply (user's command). We assume vrl_cmd is a template string which may contain {input} and {output}
    vrl_log = os.path.join(trial_dir, 'vrl_apply.log')
    vrl_output = os.path.join(trial_dir, 'repaired_vrl.img')
    vrl_cmd_filled = vrl_cmd.format(input=corrupted, output=vrl_output, trial=trial_idx)
    t0 = time.time()
    rc, out = run_cmd(vrl_cmd_filled)
    dur = time.time() - t0
    with open(vrl_log, 'w') as f:
        f.write(out or '')
    vrl_result = {'rc': rc, 'duration_s': dur, 'log': vrl_log, 'cmd': vrl_cmd_filled}

    # 4) Collect high-level metrics (size, timestamps)
    metrics = {
        'trial': trial_idx,
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'base_img_size': os.path.getsize(original),
        'corrupted_img_size': os.path.getsize(corrupted),
        'e2fsck': e2fsck_result,
        'vrl_apply': vrl_result,
    }
    with open(os.path.join(trial_dir, 'summary.json'), 'w') as f:
        json.dump(metrics, f, indent=2)
    return metrics

def main():
    p = argparse.ArgumentParser(description='Run multiple trials: seed duplicate-block faults, run e2fsck and VRL apply, collect logs')
    p.add_argument('--base-img', required=True)
    p.add_argument('--trials', type=int, default=3)
    p.add_argument('--duplicates-per-trial', type=int, default=1)
    p.add_argument('--seed', type=int, default=42)
    p.add_argument('--vrl-cmd', type=str, default='echo "No VRL command configured for {input} -> {output}"; exit 0',
                   help='Template command to run VRL apply. Use {input} and {output} in the string.')
    p.add_argument('--results-dir', default='results/experiments_dupblocks')
    args = p.parse_args()

    ensure_dir(args.results_dir)
    all_results = []
    for t in range(1, args.trials+1):
        trial_dir = os.path.join(args.results_dir, f'trial_{t:02d}')
        print('Running trial', t, '->', trial_dir)
        res = run_trial(args.base_img, trial_dir, t, args.duplicates_per_trial, args.seed + t, args.vrl_cmd)
        all_results.append(res)
        # small sleep to avoid race conditions on slow I/O
        time.sleep(0.5)
    # save aggregate
    with open(os.path.join(args.results_dir, 'aggregate.json'), 'w') as f:
        json.dump(all_results, f, indent=2)
    print('All done. Results in', args.results_dir)

if __name__ == '__main__':
    main()
