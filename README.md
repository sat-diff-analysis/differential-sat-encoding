# Evaluating CNF/SMT Encodings for SAT-Based Differential Cryptanalysis of Lightweight Ciphers

## Differential SAT Encoding & Solving - Experimental Codes

This repository contains scripts and tools for **experimental comparison of SAT/SMT/CNF encodings** and **solver performance** in differential analysis of lightweight block ciphers.

The codebase is used in the experiments and figures of our article.  


- Each cipher (e.g., `CHAM`, `SPECK`, etc.) has scripts for different encoding formats.
- Batch and utility scripts are in the root directory.

---

## Dependencies

- **Python 3.6+**
- Recommended: Linux/WSL/Unix environment for batch scripts
- SAT solvers (install as needed):
    - [CaDiCaL](https://github.com/arminbiere/cadical)
    - [CryptoMiniSat](https://github.com/msoos/cryptominisat)
    - [Treengeling](https://github.com/arminbiere/treengeling)
    - [Mallob](https://github.com/domschrei/mallob) (for distributed/parallel runs)
    - [CVC4/CVC5](https://cvc5.github.io/) (for SMT-LIB encoding)
- Python packages: `os`, `subprocess`, etc. (all standard, no extra dependencies)

---

## How to Run

### 1. Prepare Solvers
- Install your desired SAT/SMT solvers and ensure they are available in your system PATH.

### 2. Run a Model Generator

    Example: To generate CNF_LF for SPECK:

    python3 SPECK/Speck_CNF_LF.py


### 3. Batch Solve

    Use batch_solve.py or batch_mallob.py to run the solver over all instances:

    python3 batch_solve.py
    # or, for Mallob:
    python3 batch_mallob.py

### 4. Summarize Results

    Aggregate solving times using:

    python3 average_time.py

# References

    cryptosmt: https://github.com/kste/cryptosmt

    Accelerating_Automatic_Search: https://github.com/SunLing134340/Accelerating_Automatic_Search
