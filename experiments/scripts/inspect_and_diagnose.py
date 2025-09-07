#!/usr/bin/env python3
"""Inspect a snapshot JSON and produce diagnostics JSON and a human readable plan summary.
Diagnostics include: duplicate inodes, zero-sized files, files under lost+found, path depth, and simple heuristics.
"""

import argparse, json, os
from collections import defaultdict
from datetime import datetime

def load_snapshot(path):
    with open(path, 'r', encoding='utf8') as f:
        return json.load(f)

def inspect_snapshot(snap):
    files = snap.get('files', [])
    diagnostics = {
        'snapshot_id': snap.get('snapshot_id'),
        'total_files': len(files),
        'total_size': sum(f.get('size',0) for f in files),
        'duplicate_inodes': [],
        'zero_size': [],
        'lost_found': [],
        'path_depths': []
    }
    inode_map = defaultdict(list)
    for f in files:
        inode_map[f.get('inode')].append(f)
        if f.get('size',0) == 0:
            diagnostics['zero_size'].append(f)
        if f.get('path','').startswith('/lost+found'):
            diagnostics['lost_found'].append(f)
        diagnostics['path_depths'].append((f.get('path'), len(f.get('path','').split('/'))-1))
    for inode, entries in inode_map.items():
        if len(entries) > 1:
            diagnostics['duplicate_inodes'].append({
                'inode': inode,
                'entries': entries
            })
    return diagnostics

def make_plan_from_diagnostics(diag):
    # very small heuristic planner that produces actions
    actions = []
    # If duplicates, plan to mark as 'investigate' or 'merge'
    for dup in diag.get('duplicate_inodes', []):
        actions.append({'action': 'investigate_duplicates', 'inode': dup['inode'], 'reason': 'inode shared by multiple entries'})
    for f in diag.get('lost_found', []):
        actions.append({'action': 'recover_or_quarantine', 'path': f['path'], 'reason': 'entry in lost+found'})
    for f in diag.get('zero_size', []):
        actions.append({'action': 'verify_zero_size', 'path': f['path'], 'reason': 'zero-sized entry'})
    # sample summary
    summary_lines = []
    summary_lines.append(f"Snapshot: {diag.get('snapshot_id')}")
    summary_lines.append(f"Total files: {diag.get('total_files')}")
    summary_lines.append(f"Total size: {diag.get('total_size')}")
    summary_lines.append(f"Duplicate inode groups: {len(diag.get('duplicate_inodes',[]))}")
    summary_lines.append(f"Lost+found entries: {len(diag.get('lost_found',[]))}")
    summary_lines.append(f"Zero-sized files: {len(diag.get('zero_size',[]))}")
    summary_lines.append('Suggested actions:')
    for a in actions:
        summary_lines.append(f" - {a['action']}: {a.get('path', a.get('inode'))} ({a['reason']})")
    return actions, '\n'.join(summary_lines)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--snapshot', required=True)
    p.add_argument('--out', required=True, help='diagnostics JSON output path')
    p.add_argument('--summary', required=True, help='human readable summary output path')
    args = p.parse_args()

    snap = load_snapshot(args.snapshot)
    diag = inspect_snapshot(snap)
    actions, summary = make_plan_from_diagnostics(diag)

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, 'w', encoding='utf8') as f:
        json.dump({'diagnostics': diag, 'actions': actions, 'generated_at': datetime.utcnow().isoformat()+'Z'}, f, indent=2)

    with open(args.summary, 'w', encoding='utf8') as f:
        f.write(summary)

    print('Diagnostics written to', args.out)
    print('Summary written to', args.summary)

if __name__ == '__main__':
    main()
