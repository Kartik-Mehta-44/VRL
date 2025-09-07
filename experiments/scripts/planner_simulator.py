#!/usr/bin/env python3
import argparse, json, os
from datetime import datetime

def load_snapshot(path):
    with open(path, 'r', encoding='utf8') as f:
        return json.load(f)

def simulate_plan(snap):
    # Produce a list of actions with simple priorities
    files = snap.get('files', [])
    actions = []
    for f in files:
        if f.get('path','').startswith('/lost+found'):
            actions.append({'action':'quarantine','path':f['path'],'priority':1})
        elif f.get('size',0) == 0:
            actions.append({'action':'verify','path':f['path'],'priority':2})
    # If duplicate inodes detected, add investigate action
    inode_map = {}
    for f in files:
        inode_map.setdefault(f.get('inode'), []).append(f)
    for inode, ents in inode_map.items():
        if len(ents) > 1:
            actions.append({'action':'investigate','inode':inode,'count':len(ents),'priority':1})
    # sort by priority
    actions.sort(key=lambda x: x.get('priority', 99))
    return actions

def write_plan(out_plan, actions):
    os.makedirs(os.path.dirname(out_plan), exist_ok=True)
    with open(out_plan, 'w', encoding='utf8') as f:
        json.dump({'plan_generated_at': datetime.utcnow().isoformat()+'Z', 'actions': actions}, f, indent=2)

def write_summary(out_summary, actions, snap):
    os.makedirs(os.path.dirname(out_summary), exist_ok=True)
    with open(out_summary, 'w', encoding='utf8') as f:
        f.write(f"Plan summary for snapshot {snap.get('snapshot_id')}\n")
        f.write(f"Actions: {len(actions)}\n\n")
        for a in actions:
            f.write(f"- {a.get('action')} :: {a.get('path', a.get('inode', ''))} (priority={a.get('priority','')})\n")

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--snapshot', required=True)
    p.add_argument('--out-plan', required=True)
    p.add_argument('--out-summary', required=True)
    args = p.parse_args()
    snap = load_snapshot(args.snapshot)
    actions = simulate_plan(snap)
    write_plan(args.out_plan, actions)
    write_summary(args.out_summary, actions, snap)
    print('Plan and summary written')

if __name__ == '__main__':
    main()
