# Divergence Analysis (auto-generated)

Total: 129 divergences

## By Root Cause

### postcondition False Negative: quantifier_not_tracked (53)

Postcondition uses forall/exists. Quantifier instantiation not tracked in coverage — verifier proves via triggers without generating per-line coverage.

| Dataset | Task | File |
|---------|------|------|
| RQ1-GPT4 | 8 | [task_8.dfy](.eval-tmp/RQ1-GPT4/task_id_8.dfy) |
| RQ1-GPT4 | 273 | [task_273.dfy](.eval-tmp/RQ1-GPT4/task_id_273.dfy) |
| RQ1-GPT4 | 282 | [task_282.dfy](.eval-tmp/RQ1-GPT4/task_id_282.dfy) |
| RQ1-GPT4 | 429 | [task_429.dfy](.eval-tmp/RQ1-GPT4/task_id_429.dfy) |
| RQ1-GPT4 | 436 | [task_436.dfy](.eval-tmp/RQ1-GPT4/task_id_436.dfy) |
| RQ1-GPT4 | 445 | [task_445.dfy](.eval-tmp/RQ1-GPT4/task_id_445.dfy) |
| RQ1-GPT4 | 451 | [task_451.dfy](.eval-tmp/RQ1-GPT4/task_id_451.dfy) |
| RQ1-GPT4 | 728 | [task_728.dfy](.eval-tmp/RQ1-GPT4/task_id_728.dfy) |
| RQ1-GPT4 | 751 | [task_751.dfy](.eval-tmp/RQ1-GPT4/task_id_751.dfy) |
| RQ1-GPT4 | 790 | [task_790.dfy](.eval-tmp/RQ1-GPT4/task_id_790.dfy) |
| RQ2-GPT4 | 8 | [task_8.dfy](.eval-tmp/RQ2-GPT4/task_id_8.dfy) |
| RQ2-GPT4 | 470 | [task_470.dfy](.eval-tmp/RQ2-GPT4/task_id_470.dfy) |
| RQ2-GPT4 | 728 | [task_728.dfy](.eval-tmp/RQ2-GPT4/task_id_728.dfy) |
| RQ2-GPT4 | 751 | [task_751.dfy](.eval-tmp/RQ2-GPT4/task_id_751.dfy) |
| RQ2-GPT4 | 809 | [task_809.dfy](.eval-tmp/RQ2-GPT4/task_id_809.dfy) |
| RQ3-GPT4 | 8 | [task_8.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_8.dfy) |
| RQ3-GPT4 | 18 | [task_18.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_18.dfy) |
| RQ3-GPT4 | 94 | [task_94.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_94.dfy) |
| RQ3-GPT4 | 95 | [task_95.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_95.dfy) |
| RQ3-GPT4 | 106 | [task_106.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_106.dfy) |
| RQ3-GPT4 | 145 | [task_145.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_145.dfy) |
| RQ3-GPT4 | 230 | [task_230.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_230.dfy) |
| RQ3-GPT4 | 240 | [task_240.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_240.dfy) |
| RQ3-GPT4 | 251 | [task_251.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_251.dfy) |
| RQ3-GPT4 | 261 | [task_261.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_261.dfy) |
| RQ3-GPT4 | 273 | [task_273.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_273.dfy) |
| RQ3-GPT4 | 282 | [task_282.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_282.dfy) |
| RQ3-GPT4 | 284 | [task_284.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_284.dfy) |
| RQ3-GPT4 | 307 | [task_307.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_307.dfy) |
| RQ3-GPT4 | 310 | [task_310.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_310.dfy) |
| RQ3-GPT4 | 399 | [task_399.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_399.dfy) |
| RQ3-GPT4 | 401 | [task_401.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_401.dfy) |
| RQ3-GPT4 | 424 | [task_424.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_424.dfy) |
| RQ3-GPT4 | 445 | [task_445.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_445.dfy) |
| RQ3-GPT4 | 460 | [task_460.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_460.dfy) |
| RQ3-GPT4 | 565 | [task_565.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_565.dfy) |
| RQ3-GPT4 | 578 | [task_578.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_578.dfy) |
| RQ3-GPT4 | 587 | [task_587.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_587.dfy) |
| RQ3-GPT4 | 591 | [task_591.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_591.dfy) |
| RQ3-GPT4 | 618 | [task_618.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_618.dfy) |
| RQ3-GPT4 | 728 | [task_728.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_728.dfy) |
| RQ3-GPT4 | 750 | [task_750.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_750.dfy) |
| RQ3-GPT4 | 751 | [task_751.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_751.dfy) |
| RQ3-GPT4 | 769 | [task_769.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_769.dfy) |
| RQ3-PaLM2 | 8 | [task_8.dfy](.eval-tmp/RQ3-PaLM2/task_id_8.dfy) |
| RQ3-PaLM2 | 230 | [task_230.dfy](.eval-tmp/RQ3-PaLM2/task_id_230.dfy) |
| RQ3-PaLM2 | 282 | [task_282.dfy](.eval-tmp/RQ3-PaLM2/task_id_282.dfy) |
| RQ3-PaLM2 | 284 | [task_284.dfy](.eval-tmp/RQ3-PaLM2/task_id_284.dfy) |
| RQ3-PaLM2 | 310 | [task_310.dfy](.eval-tmp/RQ3-PaLM2/task_id_310.dfy) |
| RQ3-PaLM2 | 565 | [task_565.dfy](.eval-tmp/RQ3-PaLM2/task_id_565.dfy) |
| RQ3-PaLM2 | 591 | [task_591.dfy](.eval-tmp/RQ3-PaLM2/task_id_591.dfy) |
| RQ3-PaLM2 | 618 | [task_618.dfy](.eval-tmp/RQ3-PaLM2/task_id_618.dfy) |
| RQ3-PaLM2 | 728 | [task_728.dfy](.eval-tmp/RQ3-PaLM2/task_id_728.dfy) |

### invariant False Negative: oracle_error (17)

Uncovered invariant is redundant bounds for a for-loop (Dafny handles automatically). Removing it from oracle would fix this divergence.

| Dataset | Task | File |
|---------|------|------|
| RQ3-GPT4 | 94 | [task_94.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_94.dfy) |
| RQ3-GPT4 | 95 | [task_95.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_95.dfy) |
| RQ3-GPT4 | 412 | [task_412.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_412.dfy) |
| RQ3-GPT4 | 426 | [task_426.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_426.dfy) |
| RQ3-GPT4 | 436 | [task_436.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_436.dfy) |
| RQ3-GPT4 | 457 | [task_457.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_457.dfy) |
| RQ3-GPT4 | 554 | [task_554.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_554.dfy) |
| RQ3-PaLM2 | 8 | [task_8.dfy](.eval-tmp/RQ3-PaLM2/task_id_8.dfy) |
| RQ3-PaLM2 | 113 | [task_113.dfy](.eval-tmp/RQ3-PaLM2/task_id_113.dfy) |
| RQ3-PaLM2 | 230 | [task_230.dfy](.eval-tmp/RQ3-PaLM2/task_id_230.dfy) |
| RQ3-PaLM2 | 242 | [task_242.dfy](.eval-tmp/RQ3-PaLM2/task_id_242.dfy) |
| RQ3-PaLM2 | 282 | [task_282.dfy](.eval-tmp/RQ3-PaLM2/task_id_282.dfy) |
| RQ3-PaLM2 | 310 | [task_310.dfy](.eval-tmp/RQ3-PaLM2/task_id_310.dfy) |
| RQ3-PaLM2 | 728 | [task_728.dfy](.eval-tmp/RQ3-PaLM2/task_id_728.dfy) |
| RQ3-PaLM2 | 790 | [task_790.dfy](.eval-tmp/RQ3-PaLM2/task_id_790.dfy) |
| RQ3-PaLM2 | 792 | [task_792.dfy](.eval-tmp/RQ3-PaLM2/task_id_792.dfy) |
| RQ3-PaLM2 | 808 | [task_808.dfy](.eval-tmp/RQ3-PaLM2/task_id_808.dfy) |

### postcondition False Positive: trivially_true_spec (16)

Postcondition appears too weak to capture full behavior. Coverage complete but spec is insufficient.

| Dataset | Task | File |
|---------|------|------|
| RQ1-GPT4 | 9 | [task_9.dfy](.eval-tmp/RQ1-GPT4/task_id_9.dfy) |
| RQ1-GPT4 | 82 | [task_82.dfy](.eval-tmp/RQ1-GPT4/task_id_82.dfy) |
| RQ1-GPT4 | 105 | [task_105.dfy](.eval-tmp/RQ1-GPT4/task_id_105.dfy) |
| RQ1-GPT4 | 133 | [task_133.dfy](.eval-tmp/RQ1-GPT4/task_id_133.dfy) |
| RQ1-GPT4 | 287 | [task_287.dfy](.eval-tmp/RQ1-GPT4/task_id_287.dfy) |
| RQ1-GPT4 | 432 | [task_432.dfy](.eval-tmp/RQ1-GPT4/task_id_432.dfy) |
| RQ1-GPT4 | 479 | [task_479.dfy](.eval-tmp/RQ1-GPT4/task_id_479.dfy) |
| RQ1-GPT4 | 577 | [task_577.dfy](.eval-tmp/RQ1-GPT4/task_id_577.dfy) |
| RQ1-GPT4 | 578 | [task_578.dfy](.eval-tmp/RQ1-GPT4/task_id_578.dfy) |
| RQ1-GPT4 | 626 | [task_626.dfy](.eval-tmp/RQ1-GPT4/task_id_626.dfy) |
| RQ2-GPT4 | 273 | [task_273.dfy](.eval-tmp/RQ2-GPT4/task_id_273.dfy) |
| RQ2-GPT4 | 389 | [task_389.dfy](.eval-tmp/RQ2-GPT4/task_id_389.dfy) |
| RQ2-GPT4 | 586 | [task_586.dfy](.eval-tmp/RQ2-GPT4/task_id_586.dfy) |
| RQ3-PaLM2 | 89 | [task_89.dfy](.eval-tmp/RQ3-PaLM2/task_id_89.dfy) |
| RQ3-PaLM2 | 452 | [task_452.dfy](.eval-tmp/RQ3-PaLM2/task_id_452.dfy) |
| RQ3-PaLM2 | 479 | [task_479.dfy](.eval-tmp/RQ3-PaLM2/task_id_479.dfy) |

### postcondition False Negative: multi_method (16)

Multi-method/predicate/function program. Coverage attribution across units may miss postcondition dependencies.

| Dataset | Task | File |
|---------|------|------|
| RQ3-GPT4 | 2 | [task_2.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_2.dfy) |
| RQ3-GPT4 | 105 | [task_105.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_105.dfy) |
| RQ3-GPT4 | 133 | [task_133.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_133.dfy) |
| RQ3-GPT4 | 161 | [task_161.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_161.dfy) |
| RQ3-GPT4 | 170 | [task_170.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_170.dfy) |
| RQ3-GPT4 | 249 | [task_249.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_249.dfy) |
| RQ3-GPT4 | 412 | [task_412.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_412.dfy) |
| RQ3-GPT4 | 426 | [task_426.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_426.dfy) |
| RQ3-GPT4 | 436 | [task_436.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_436.dfy) |
| RQ3-GPT4 | 476 | [task_476.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_476.dfy) |
| RQ3-GPT4 | 554 | [task_554.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_554.dfy) |
| RQ3-GPT4 | 557 | [task_557.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_557.dfy) |
| RQ3-GPT4 | 623 | [task_623.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_623.dfy) |
| RQ3-GPT4 | 790 | [task_790.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_790.dfy) |
| RQ3-GPT4 | 804 | [task_804.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_804.dfy) |
| RQ3-PaLM2 | 790 | [task_790.dfy](.eval-tmp/RQ3-PaLM2/task_id_790.dfy) |

### precondition False Negative: quantifier_not_tracked (14)

Precondition not referenced in proof trace but semantically required. Verifier uses it implicitly to constrain input space.

| Dataset | Task | File |
|---------|------|------|
| RQ1-GPT4 | 276 | [task_276.dfy](.eval-tmp/RQ1-GPT4/task_id_276.dfy) |
| RQ2-GPT4 | 240 | [task_240.dfy](.eval-tmp/RQ2-GPT4/task_id_240.dfy) |
| RQ3-GPT4 | 94 | [task_94.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_94.dfy) |
| RQ3-GPT4 | 261 | [task_261.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_261.dfy) |
| RQ3-GPT4 | 262 | [task_262.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_262.dfy) |
| RQ3-GPT4 | 304 | [task_304.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_304.dfy) |
| RQ3-GPT4 | 401 | [task_401.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_401.dfy) |
| RQ3-GPT4 | 424 | [task_424.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_424.dfy) |
| RQ3-GPT4 | 460 | [task_460.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_460.dfy) |
| RQ3-GPT4 | 591 | [task_591.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_591.dfy) |
| RQ3-GPT4 | 618 | [task_618.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_618.dfy) |
| RQ3-GPT4 | 622 | [task_622.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_622.dfy) |
| RQ3-PaLM2 | 282 | [task_282.dfy](.eval-tmp/RQ3-PaLM2/task_id_282.dfy) |
| RQ3-PaLM2 | 618 | [task_618.dfy](.eval-tmp/RQ3-PaLM2/task_id_618.dfy) |

### invariant False Negative: quantifier_not_tracked (6)

Invariant uses forall/exists. Quantifier instantiation not tracked in coverage.

| Dataset | Task | File |
|---------|------|------|
| RQ1-GPT4 | 451 | [task_451.dfy](.eval-tmp/RQ1-GPT4/task_id_451.dfy) |
| RQ2-GPT4 | 751 | [task_751.dfy](.eval-tmp/RQ2-GPT4/task_id_751.dfy) |
| RQ3-GPT4 | 284 | [task_284.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_284.dfy) |
| RQ3-GPT4 | 555 | [task_555.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_555.dfy) |
| RQ3-GPT4 | 751 | [task_751.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_751.dfy) |
| RQ3-PaLM2 | 284 | [task_284.dfy](.eval-tmp/RQ3-PaLM2/task_id_284.dfy) |

### invariant False Positive: trivially_true_spec (4)

Invariant is trivially true. Coverage complete but invariant doesn't constrain loop meaningfully.

| Dataset | Task | File |
|---------|------|------|
| RQ1-GPT4 | 95 | [task_95.dfy](.eval-tmp/RQ1-GPT4/task_id_95.dfy) |
| RQ1-GPT4 | 479 | [task_479.dfy](.eval-tmp/RQ1-GPT4/task_id_479.dfy) |
| RQ1-GPT4 | 809 | [task_809.dfy](.eval-tmp/RQ1-GPT4/task_id_809.dfy) |
| RQ2-GPT4 | 443 | [task_443.dfy](.eval-tmp/RQ2-GPT4/task_id_443.dfy) |

### precondition False Negative: multi_method (2)

Multi-method program. Precondition may be used by helper but not tracked in main method's proof.

| Dataset | Task | File |
|---------|------|------|
| RQ3-GPT4 | 170 | [task_170.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_170.dfy) |
| RQ3-GPT4 | 577 | [task_577.dfy](dafny-synthesis/MBPP-DFY-153/src/task_id_577.dfy) |

### postcondition False Positive: oracle_error (1)

Postcondition uses quantifiers and appears strong. Oracle may be incorrect.

| Dataset | Task | File |
|---------|------|------|
| RQ1-GPT4 | 809 | [task_809.dfy](.eval-tmp/RQ1-GPT4/task_id_809.dfy) |
