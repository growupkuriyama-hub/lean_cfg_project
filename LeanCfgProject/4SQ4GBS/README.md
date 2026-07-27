# All-Python proof package

This archive certifies the theorem on generalized binary squares with
`11`-free (fibbinary) roots without any C++ source code or executable.

## Requirements

- Python 3.13 (tested; recent Python 3 versions may also work)
- NumPy 2.3.5
- Numba 0.65.1

Install the two dependencies with:

```bash
python -m pip install -r requirements.txt
```

Numba JIT-compiles the performance-critical antichain loops.  Thus no C++
compiler or C++ source is needed, although the first verifier run includes a
short JIT-compilation step.

## One-command verification

```bash
python run_all.py
```

This performs:

1. a direct finite sumset check below `2^14`;
2. regression comparisons between the folded NFA and direct enumeration;
3. regeneration of the odd and even graph certificates;
4. backward-antichain verification of both infinite inclusions.

The expected final line is:

```text
ALL PYTHON CERTIFICATES PASSED
```

## Individual commands

```bash
python finite_check.py --bits 14
python regression_check.py
python build_graphs.py
python verify_antichain.py
```

The verifier accepts explicit certificate paths as well:

```bash
python verify_antichain.py odd_graph.txt even_graph.txt
```

Use `--threads N` to control the number of Numba worker threads.  The default
is at most four.  On the test environment, each infinite inclusion check took
about 7--8 seconds after loading/JIT and used roughly 0.5 GB of memory.

## Files

- `folded_nfa.py`: exact folded-NFA specification;
- `finite_check.py`: direct finite sumset verification;
- `regression_check.py`: independent small-length comparisons;
- `build_graphs.py`: graph-certificate generator;
- `verify_antichain.py`: Python/Numba backward-antichain verifier;
- `odd_graph.txt`, `even_graph.txt`: generated finite certificates;
- `run_all.py`: one-command driver.
