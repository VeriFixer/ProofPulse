# TODO: Assertion Dataset & Evaluation

## Known Eval Failures

| Task | Issue | Root Cause |
|---|---|---|
| 82 (SphereVolume) | Classified strong, oracle says weak | Simple arithmetic — all lines used but spec is weak |
| 126 (sumOfCommonDivisors) | inv=strong, oracle=weak | Code lines in loop body not flagged as unused |
| 273 (SubtractSeqs) | post=weak, oracle=strong | `forall` quantifier limitation in attribution |
| 282 (SubtractArrays) | post=weak, oracle=strong | Same forall issue + `new` keyword (allocation breaks tracing) |
| 309 (Max) | post=weak, oracle=strong | Simple assignment coverage bug |
| NegativeNumbers | pre=required, oracle=optional | Several preconditions actually not required |

## Precondition Detection
Works well overall. Example: CylinderVolume correctly identifies `radius >= 0` as optional (radius² always ≥ 0).

## Paper Improvements Plan

1. **Dataset expansion** — more examples with 2+ missing assertions, sampling across different assertion counts
2. **Assertion count prediction** — pre-step to predict how many assertions needed, compare with hardcoded "max 2"
3. **Prompt improvements** — reveal/by clauses, indexing examples, method/lemma/function signatures, proof idiom simplification
4. **Model experiments** — try Qwen (local), possible fine-tuning

## Paper Section Trim Notes

Best cut candidates: Background & Motivation (repeats intro), Tool Architecture steps 2-3 (repeat formalism), Table 2 (per-dataset preconditions — combined row in Table 1 suffices).
