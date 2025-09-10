#!/usr/bin/env python3
import subprocess, json, re

IMAGE = "images/disk1.img"

def run_debugfs(cmd):
    """Run a single debugfs command and return output"""
    result = subprocess.run(
        ["debugfs", "-R", cmd, IMAGE],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()

def parse_superblock():
    out = run_debugfs("show_super_stats")
    data = {}
    for line in out.splitlines():
        if ":" in line:
            key, val = line.split(":", 1)
            data[key.strip()] = val.strip()
    return data

def parse_inode(inode_num):
    out = run_debugfs(f"stat <{inode_num}>")
    data = {"inode": inode_num, "raw": out}
    # crude regex parse for size, type, blockcount
    m = re.search(r"Type:\s+(\w+)", out)
    if m: data["type"] = m.group(1)
    m = re.search(r"Size:\s+(\d+)", out)
    if m: data["size"] = int(m.group(1))
    m = re.search(r"Blockcount:\s+(\d+)", out)
    if m: data["blockcount"] = int(m.group(1))
    return data

def parse_bitmaps():
    return {
        "block_bitmap": run_debugfs("show_block_bitmap"),
        "inode_bitmap": run_debugfs("show_inode_bitmap")
    }

if __name__ == "__main__":
    metadata = {
        "superblock": parse_superblock(),
        "inode_12": parse_inode(12),
        "bitmaps": parse_bitmaps(),
    }
    with open("metadata.json", "w") as f:
        json.dump(metadata, f, indent=2)
    print("✅ Metadata dumped to metadata.json")
