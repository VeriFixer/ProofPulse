# Coverage that counts what checks rely on (branch `wf-status-inheritance`)

**The rule.** An expression that is needed only so that another expression E makes sense (E is well-defined, or a
call in E may be made) gets the better of its own status and E's status. Checks in code make what they use covered,
since code is not up for removal.

**The guarantee it gives:** delete everything ProofPulse marks **Uncovered**, all at once, and the program still
verifies. Each file below shows the old and new statuses, and what Dafny says when you delete everything marked
Uncovered (checked in `proofpulse-ci`).

**How to look at them.** The installed VS Code extension is the new version: open a file and save it, or run
*ProofPulse: Run Coverage Analysis*. The tables give the old statuses for comparison. Files 03 and 04 are complex
tests from `dataset/tests`.

**Across the repo's Dafny files** (135 files: integration tests, dataset files, study items, demos), deleting all
Uncovered clauses broke verification in 27 files before and 2 after. Both are trigger cases (file 07).

---

## `01_wellformedness_cases.dfy`

Source: `core/src/__tests__/fixtures/wellformedness.dfy (unit-test fixture)`

All the cases of the rule in one small file. The lemma `SumStep` is never called, so its `ensures` is CovTest; `n < |s|` makes that `ensures` well-defined, so it is treated like what proves it: covered, as `0 <= n` already was (old: Uncovered, but deleting it breaks verification). In `Total`, the bound invariant only serves the uncovered invariant `t == sum(s, i)`, so both stay Uncovered and can go together. In `Grow`, `x !in s` only serves the precondition of a lemma call, so it gets the call's status (CovTest). `UseGet` and `Get`: `Get`'s `ensures` is needed by `UseGet`'s postcondition, so it stays covered.

| Line:col | Expression | Old | New |
|---|---|---|---|
| 1:1 | `function sum(s: seq<int>, n: int): int …` | CovTest | **—** |
| 24:17 | `n < \|s\|` | Uncovered | **—** |
| 35:20 | `i <= \|s\|` | Uncovered | **—** |
| 49:12 | `x !in s` | Uncovered | **CovTest** |

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old verification FAILS ❌ · new still verifies ✅

Old failure: `Error: function precondition could not be proved`

---

## `02_MissingNumber_lemma_requires.dfy`

Source: `Paper D study item CB`

The case that started this. `n < arr.Length` in the unused lemma `SumProperty` was Uncovered, but deleting it breaks the lemma's own `ensures`. Now it is covered, like `0 <= n`, which proves that `ensures`. The bound invariant `0 <= i <= arr.Length` is reported once, as a whole clause.

| Line:col | Expression | Old | New |
|---|---|---|---|
| 16:24 | `i <= arr.Length` | Uncovered | **—** |
| 28:1 | `function sum(arr: array<int>, n: int): int …` | CovTest | **—** |
| 36:19 | `n < arr.Length` | Uncovered | **—** |

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old verification FAILS ❌ · new still verifies ✅

Old failure: `Error: function precondition could not be proved`

---

## `03_test_complex_7_guess.dfy`

Source: `dataset/tests/test_complex_7 (complex test)`

Complex test. `Guess`'s `ensures` were Uncovered, but `Main` uses them (e.g. `known == false` for the precondition of its second `Guess` call). `Main` is only a test (no postcondition), so they are now CovTest: kept, but only tests need them. An `ensures` is covered only when some caller needs the result for its own proof.

| Line:col | Expression | Old | New |
|---|---|---|---|
| 8:9 | `j,k := 1,3;` | — | **CovTest** |
| 43:13 | `secret == x` | — | **CovTest** |
| 44:13 | `known == false` | — | **CovTest** |
| 45:13 | `count == 0` | — | **CovTest** |
| 54:14 | `known == false` | CovTest | **—** |
| 56:17 | `result == true` | Uncovered | **CovTest** |
| 56:35 | `known == true` | Uncovered | **CovTest** |
| 58:17 | `result == false` | Uncovered | **CovTest** |
| 58:36 | `known == false` | Uncovered | **CovTest** |
| 59:13 | `count == old(count) + 1` | Uncovered | **CovTest** |
| 59:40 | `guesses == count` | Uncovered | **CovTest** |
| 76:13 | `testObject : Secret := new Secret.Init(5);` | — | **CovTest** |

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old verification FAILS ❌ · new still verifies ✅

Old failure: `Error: a precondition for this call could not be proved`

---

## `04_test_complex_2_lemma_calls.dfy`

Source: `dataset/tests/test_complex_2 (complex test)`

Complex test. The lemma calls `CardinalitySubsetLt` are CovTest; the invariant parts their preconditions need (`Special in I`, `Special !in S`, `S <= I`) were Uncovered and now get the calls' status. What only serves the unused `assert`s (`S < P`, `I <= P`, the `switch` invariant) stays Uncovered. The lemma's own `requires A < B` is now covered: its body needs it (`var b :| b in B && b !in A`). Its `ensures |A| < |B|` has two nodes, the lemma's own proof (covered) and a copy seen from the caller (unused); the expression view now keeps the best of the two, as the line view always did (yesterday's per-expression commit kept the worst, which was a bug).

| Line:col | Expression | Old | New |
|---|---|---|---|
| 4:12 | `A < B` | CovTest | **—** |
| 5:11 | `\|A\| < \|B\|` | Uncovered | **CovTest** |
| 30:15 | `count > 0 ==> Special in I` | Uncovered | **—** |
| 30:29 | `Special in I` | — | **CovTest** |
| 31:15 | `Special !in S` | Uncovered | **CovTest** |
| 31:32 | `S < P` | — | **Uncovered** |
| 31:41 | `S <= I` | — | **CovTest** |
| 31:46 | `I <= P` | — | **Uncovered** |

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old verification FAILS ❌ · new still verifies ✅

Old failure: `Error: a precondition for this call could not be proved`

---

## `05_binary_search_guard_invariant.dfy`

Source: `dataset/dafny_dataset_files/Clover_binary_search.dfy`

`0 <= lo` was Uncovered, but the covered invariant `forall i :: 0 <= i < lo ==> a[i] < key` needs it for `a[i]` to be in range. Now it is covered. The CovTest `ensures 0 <= n <= a.Length` stays CovTest (it only serves other CovTest `ensures`).

| Line:col | Expression | Old | New |
|---|---|---|---|
| 3:11 | `0 <= n` | CovTest | **—** |
| 3:16 | `n <= a.Length` | CovTest | **—** |
| 15:15 | `0 <= lo` | Uncovered | **—** |

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old still verifies ✅ · new nothing marked Uncovered

---

## `06_append_forall_invariant.dfy`

Source: `dataset/tests/test_lurking_axioms`

The bound invariant `0 <= i <= a.Length` was Uncovered; the covered `forall` invariant needs it for `c[ii]` and `a[ii]` to be in range. Now covered: nothing in the file is marked removable, and that is right.

| Line:col | Expression | Old | New |
|---|---|---|---|
| 7:15 | `0 <= i` | Uncovered | **—** |
| 7:20 | `i <= a.Length` | Uncovered | **—** |

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old verification FAILS ❌ · new nothing marked Uncovered

Old failure: `Error: index out of range`

---

## `07_LIMITATION_trigger_witness.dfy`

Source: `dataset/tests/bug_trigger_quantiffers_not_tracked`

**Not fixed (limitation):** `assert(IsSublistAt(sub,main,i))` only supplies the witness term for `exists k :: IsSublistAt(sub, main, k)`. The unsat core never names it, so it stays Uncovered, and deleting it breaks verification. This is the trigger / lurking-axiom problem; the rule here cannot see it.

No status changed.

Only expressions whose status changed are listed; — means not flagged (fully covered, or folded into a whole clause).

**Delete everything marked Uncovered, all at once, then `dafny verify`:** old verification FAILS ❌ · new verification FAILS ❌

Old failure: `Error: a postcondition could not be proved on this return path`

New failure: `Error: a postcondition could not be proved on this return path`

---
