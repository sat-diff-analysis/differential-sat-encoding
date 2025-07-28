#!/usr/bin/env python3
import subprocess
import argparse
import re
from pathlib import Path

STATUS = {
    10: "SAT",
    20: "UNSAT"
}

def natural_key(path: Path):
    """
    Split the filename into text and numbers so that
    file2.cnf < file10.cnf in the sort order.
    """
    parts = re.split(r'(\d+)', path.name)
    return [int(p) if p.isdigit() else p.lower() for p in parts]

def main():
    parser = argparse.ArgumentParser(
        description="Run CaDiCaL on all .cnf files in a directory multiple times,"
                    " outputting all results into a 'solutions/' folder."
    )
    parser.add_argument(
        "directory",
        type=Path,
        help="Path to the directory containing .cnf files"
    )
    parser.add_argument(
        "-r", "--runs",
        type=int,
        default=5,
        help="Number of times to iterate over all files (default: 10)"
    )
    parser.add_argument(
        "-s", "--solver",
        type=Path,
        default=Path("/home/user/cadical-master/build/cadical"),
        #default=Path("/home/user/lingeling/treengeling"),
        help="Path to the CaDiCaL binary"
    )
    args = parser.parse_args()

    cnf_dir = args.directory
    if not cnf_dir.is_dir():
        print(f"Error: '{cnf_dir}' is not a directory.")
        return

    # find and sort .cnf files naturally
    cnf_files = sorted(cnf_dir.glob("*.cnf"), key=natural_key)
    if not cnf_files:
        print(f"No .cnf files found in '{cnf_dir}'.")
        return

    # prepare solutions folder
    solutions_dir = cnf_dir / "solutions"
    solutions_dir.mkdir(exist_ok=True)

    for run in range(1, args.runs + 1):
        print(f"\n=== Run {run}/{args.runs} ===")
        for cnf_file in cnf_files:
            out_name = cnf_file.stem + f".run{run}.out"
            out_file = solutions_dir / out_name
            print(f"Solving {cnf_file.name} → solutions/{out_name} ... ", end="", flush=True)

            with open(out_file, "w") as fout:
                result = subprocess.run(
                    [str(args.solver), str(cnf_file)],
                    stdout=fout,
                    stderr=subprocess.STDOUT
                )

            code = result.returncode
            if code in STATUS:
                print(STATUS[code])
            elif code == 0:
                print("OK")
            else:
                print(f"failed (exit {code})")

    print("\nAll runs completed. Outputs are in:", solutions_dir)

if __name__ == "__main__":
    main()

