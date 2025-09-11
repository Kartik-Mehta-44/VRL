#!/usr/bin/env python3
import argparse, json, os

def load_metadata():
    if os.path.exists("metadata.json"):
        with open("metadata.json") as f:
            data = json.load(f)
            return {
                "block_bitmap": data.get("group_desc", {}).get("block_bitmap", 9),
                "inode_bitmap": data.get("group_desc", {}).get("inode_bitmap", 25),
                "inode_table": data.get("group_desc", {}).get("inode_table", 41),
            }
    return {"block_bitmap": 9, "inode_bitmap": 25, "inode_table": 41}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["manual", "auto"], default="manual")
    args = parser.parse_args()

    # superblock mock (just for demo)
    superblock = {"inodes": 16384, "blocks": 16384, "block_size": 4096}

    if args.mode == "auto":
        group_desc = load_metadata()
    else:
        group_desc = {"block_bitmap": 9, "inode_bitmap": 25, "inode_table": 41}

    # simulate bitmap flip
    bitmap = [0] * 32
    before = bitmap[10]
    bitmap[10] ^= 16
    after = bitmap[10]

    report = {
        "mode": args.mode,
        "superblock": superblock,
        "group_desc": group_desc,
        "modified_block_bitmap": bitmap
    }

    with open("fix_report.json", "w") as f:
        json.dump(report, f, indent=2)

    print(f"Mode: {args.mode}")
    print("Superblock:", superblock)
    print("Group Desc:", group_desc)
    print(f"Before flip: {before}")
    print(f"After flip: {after}")
    print("✅ Simulation done. Changes written to fix_report.json (in-memory only)")

if __name__ == "__main__":
    main()
