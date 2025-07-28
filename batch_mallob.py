#!/usr/bin/env python3
import subprocess
import argparse
import re
import os
from pathlib import Path

def natural_key(path: Path):
    # numeric‐aware split, so file2.cnf < file10.cnf
    parts = re.split(r"(\d+)", path.name)
    return [int(p) if p.isdigit() else p.lower() for p in parts]

def main():
    p = argparse.ArgumentParser(
        description="Batch‐run Mallob on all .cnf files in a directory multiple times"
    )
    p.add_argument("directory", type=Path,
                   help="Directory containing .cnf files")
    p.add_argument("-r", "--runs", type=int, default=5,
                   help="How many full passes over the file set (default: 5)")
    p.add_argument("-m", "--mallob", type=Path,
                   default=Path("/home/user/mallob/build/mallob"),
                   help="Path to the Mallob binary")
    p.add_argument("--np", type=int, default=1,
                   help="mpirun -np <N> (default: 1)")
    p.add_argument("--bind-to", default="hwthread",
                   help="mpirun --bind-to <X> (default: hwthread)")
    p.add_argument("--map-by", default="ppr:1:node:pe=24",
                   help="mpirun --map-by <Y> (default: ppr:1:node:pe=24)")
    p.add_argument("-t", "--threads", type=int, default=24,
                   help="Mallob -t=<threads> (default: 24)")
    p.add_argument("-s", "--satsolver", default="kcl",
                   help="Mallob -satsolver=<solver> (default: kcl)")
    args = p.parse_args()

    cnf_dir = args.directory
    if not cnf_dir.is_dir():
        print(f"Error: {cnf_dir} is not a directory"); return

    # gather & sort
    cnfs = sorted(cnf_dir.glob("*.cnf"), key=natural_key)
    if not cnfs:
        print(f"No .cnf files found in {cnf_dir}"); return

    # make solutions folder
    sol_dir = cnf_dir / "solutions"
    sol_dir.mkdir(exist_ok=True)

    # prepare MPI env
    env = os.environ.copy()
    env["RDMAV_FORK_SAFE"] = "1"

    for run in range(1, args.runs + 1):
        print(f"\n=== Run {run}/{args.runs} ===")
        for cnf in cnfs:
            out_name = f"{cnf.stem}.run{run}.out"
            out_path = sol_dir / out_name
            print(f"Running {cnf.name} → solutions/{out_name} ... ", end="", flush=True)

            # build mpirun + mallob command
            cmd = [
                "mpirun",
                "-np", str(args.np),
                "--bind-to", args.bind_to,
                "--map-by", args.map_by,
                str(args.mallob),
                f"-mono={cnf.name}",
                f"-t={args.threads}",
                f"-satsolver={args.satsolver}"
            ]

            # run in the cnf_dir so that -mono=<filename> resolves
            try:
                with open(out_path, "w") as fout:
                    proc = subprocess.run(
                        cmd,
                        cwd=cnf_dir,
                        stdout=fout,
                        stderr=subprocess.PIPE,
                        env=env,
                        text=True
                    )
            except Exception as e:
                print(f"ERROR launching Mallob: {e}")
                continue

            if proc.returncode != 0:
                print(f"ERROR (exit {proc.returncode})")
                # you can also print proc.stderr if you want details
                continue

            # detect SAT/UNSAT
            try:
                content = out_path.read_text().upper()
                if "UNSAT" in content:
                    print("UNSAT")
                elif "SAT" in content:
                    print("SAT")
                else:
                    print("UNKNOWN")
            except Exception as e:
                print(f"ERR reading output: {e}")

    print("\nBatch complete. All outputs in:", sol_dir)

if __name__ == "__main__":
    main()

