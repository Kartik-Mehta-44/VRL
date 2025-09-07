#!/usr/bin/env python3
import argparse, os, json
from datetime import datetime

SAMPLE1 = {
    "snapshot_id": "demo-snap-001",
    "created": None,
    "files": [
        {"path": "/file1.txt", "inode": 101, "size": 128, "bad": False},
        {"path": "/file2.txt", "inode": 102, "size": 256, "bad": False},
        {"path": "/lost+found/unknown", "inode": 103, "size": 0, "bad": True},
        {"path": "/dup1.txt", "inode": 104, "size": 64, "bad": False},
        {"path": "/dup2.txt", "inode": 104, "size": 64, "bad": False}
    ]
}

SAMPLE2 = {
    "snapshot_id": "demo-snap-002",
    "created": None,
    "files": [
        {"path": "/a/b/c/d.txt", "inode": 201, "size": 512, "bad": False},
        {"path": "/a/b/.hidden", "inode": 202, "size": 1, "bad": False},
        {"path": "/lost+found/strange", "inode": 203, "size": 0, "bad": True}
    ]
}

def write_sample(obj, path):
    obj['created'] = datetime.utcnow().isoformat() + 'Z'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf8') as f:
        json.dump(obj, f, indent=2)
    print('Wrote', path)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', required=True, help='output directory for sample snapshots')
    args = p.parse_args()
    os.makedirs(args.out, exist_ok=True)
    write_sample(SAMPLE1, os.path.join(args.out, 'sample_snapshot_1.json'))
    write_sample(SAMPLE2, os.path.join(args.out, 'sample_snapshot_2.json'))

if __name__ == '__main__':
    main()
