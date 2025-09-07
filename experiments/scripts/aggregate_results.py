#!/usr/bin/env python3
import argparse, csv, json, os

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--diagnostics', required=True)
    p.add_argument('--plan', required=True)
    p.add_argument('--out', required=True)
    args = p.parse_args()
    with open(args.diagnostics, 'r', encoding='utf8') as f:
        diag = json.load(f)
    with open(args.plan, 'r', encoding='utf8') as f:
        plan = json.load(f)
    rows = [
        ('metric','value'),
        ('snapshot_id', diag.get('diagnostics',{}).get('snapshot_id','')),
        ('total_files', diag.get('diagnostics',{}).get('total_files',0)),
        ('total_size', diag.get('diagnostics',{}).get('total_size',0)),
        ('duplicate_groups', len(diag.get('diagnostics',{}).get('duplicate_inodes',[]))),
        ('lost_found_entries', len(diag.get('diagnostics',{}).get('lost_found',[]))),
        ('planned_actions', len(plan.get('actions',[])))
    ]
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, 'w', newline='', encoding='utf8') as f:
        writer = csv.writer(f)
        writer.writerows(rows)
    print('Aggregated metrics written to', args.out)

if __name__ == '__main__':
    main()
