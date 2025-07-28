#!/usr/bin/env python3
import re
import argparse
from pathlib import Path
import sys
from collections import defaultdict


TIME_PATTERNS = [
    re.compile(r"total real time since initialization:\s*([\d.]+)\s*seconds"),
    re.compile(r"total process time since initialization:\s*([\d.]+)\s*seconds"),
    re.compile(r"RESPONSE_TIME.*?\s+([\d]+\.\d+)"),
    re.compile(r"^c\s*([\d.]+)\s+wall clock time"),
    re.compile(r"^c\s*Total time \(this thread\)\s*:\s*([\d.]+)"),
]

def parse_time_from_log(path: Path):
    with path.open() as f:
        for line in f:
            for pattern in TIME_PATTERNS:
                m = pattern.search(line)
                if m:
                    return float(m.group(1))
    return None

def extract_round_weight(filename):

    m = re.search(r"(?:Problem-)?Round(\d+)[-_]Probability(\d+)", filename)
    if m:
        return int(m.group(1)), int(m.group(2))


    m = re.search(r"(?:output[_\-])(\d+)[_\-](\d+)", filename)
    if m:
        return int(m.group(1)), int(m.group(2))

    return None, None

def main():
    parser = argparse.ArgumentParser(description="Compute average solve time per (round, weight)")
    parser.add_argument("directory", type=Path, help="Directory containing .out files")
    parser.add_argument("-n", "--runs", type=int, default=5, help="Expected number of runs per weight")
    args = parser.parse_args()

    if not args.directory.is_dir():
        print(f"Error: {args.directory} is not a directory", file=sys.stderr)
        sys.exit(1)

    groups = defaultdict(list)
    total_time = 0.0
    total_files = 0

    for file in sorted(args.directory.glob("*.out")):
        time_val = parse_time_from_log(file)
        if time_val is None:
            print(f"Warning: no time found in {file.name}", file=sys.stderr)
            continue

        round_id, weight = extract_round_weight(file.name)
        if weight is None:
            print(f"Warning: could not extract round/weight from {file.name}", file=sys.stderr)
            continue

        key = (round_id, weight)
        groups[key].append(time_val)
        total_time += time_val
        total_files += 1

    print("\n=== Average solving time per (round, weight) ===")
    for (round_id, weight), times in sorted(groups.items()):
        label = f"Round {round_id}" if round_id is not None else "Unknown round"
        avg = sum(times) / len(times)
        print(f"{label} - Weight {weight}: {avg:.2f} s over {len(times)} runs")

    print(f"\nFound {total_files} log files, summed time = {total_time:.2f} s")
    print(f"Average over {len(groups)} groups = {total_time / len(groups):.2f} s")
    

if __name__ == "__main__":
    main()

