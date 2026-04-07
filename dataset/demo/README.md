# Demo Bundle

This folder groups the ready-made demo assets used in the README.

Files:
- `_USECASE_demo_showcase_small_examples.dfy` - compact positive examples
- `_USECASE_demo_bugs_limitations.dfy` - bugs, limitations, and main difficulties
- `_USECASE_verus_fib_pow_translation.dfy` - Verus-to-Dafny translation of the Fibonacci/power proof
- `test_fully_use_postcondition/` - concrete source, generated artifacts, and write-up for the fully-use-postcondition example

Quick pointers:
- Use `_USECASE_demo_showcase_small_examples.dfy` for positive coverage examples.
- Use `_USECASE_demo_bugs_limitations.dfy` for bug-style and limitation examples.
- Use `_USECASE_verus_fib_pow_translation.dfy` for a cross-language proof translation demo.

Inside `test_fully_use_postcondition/`:
- `test_fully_use_postcondition.dfy` - Dafny source used for the write-up
- `output.bpl` - generated Boogie program
- `output.smt2` - generated SMT-LIB output
- `output.smt2.1` - solver input used for the unsat-core explanation
- `prover_log.txt` - Dafny prover log
- `cov/` - coverage artifacts
- `WRITEUP_fully_use_postcondition_mapping.md` - concrete source -> Boogie -> Z3 write-up
