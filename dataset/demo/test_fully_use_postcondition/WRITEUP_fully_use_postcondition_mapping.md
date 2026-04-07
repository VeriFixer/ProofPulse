# Fully-Use-Postcondition Deep Write-Up

This write-up uses the example in:
- test_fully_use_postcondition.dfy

Goal:
1. Track source facts into Boogie.
2. Track Boogie facts into Z3 encoding.
3. Extract unsat core.
4. Walk the unsat core back to source meaning.

## 1) Source Program (Dafny)

Key source facts:
- In `ret32`, postcondition: `x == 32`.
- In `ret32`, assignment: `x := 32`.
- In `Main`, call: `n := ret32(5)`.
- In `Main`, assertion: `assert n == 32`.

From prover log summary:
- `ret32` proof dependencies include the ensures clause and assignment line.
- `Main` proof dependencies include "ensures clause ... from call" and the assertion itself.

## 2) Dafny -> Boogie Mapping

Relevant Boogie facts from output.bpl:

### 2.1 Call-level postcondition gets a Boogie id
- In call procedure for ret32:
  - `ensures {:id "id1"} x#0 == LitInt(32);`

Interpretation:
- Source `ensures x==32` is represented at call boundary with `id1`.

### 2.2 Main call and assertion ids
- In Main implementation:
  - `call {:id "id5"} $rhs##0 := Call$$_module.__default.ret32(a##0);`
  - `assert {:id "id7"} n#0 == LitInt(32);`

Interpretation:
- Source call gets `id5`.
- Source assertion `assert n==32` gets `id7`.

### 2.3 Source location recovery
Boogie includes capture markers:
- initial state and statement-local captureState entries for source lines in:
  - ret32 body
  - Main call/assert region

These are the anchors used to map back to source spans.

## 3) Boogie -> Z3 Encoding Mapping

In output.smt2.1, the key named assumptions are:
- `aux$$assume$$id1$id5$ensures`
- `aux$$assert$$id7`

Notice the first one is merged:
- It combines call-id and ensures-id (`id1` + `id5`) in one named atom.

This matches the known behavior where call + ensures can be merged in SMT-level naming.

Also in the verification condition:
- `= $generated@@101 ($generated@@46 5)` corresponds to call argument `5`.
- `(=> $generated@@103 (= $generated@@104 ($generated@@46 32)))` uses the named atom for the ensures-from-call relation.
- `(and $generated@@105 (= $generated@@104 ($generated@@46 32)))` ties the assertion atom to the expected value relation.

Practical interpretation:
- `$generated@@104` acts as the symbolic return value used in Main.
- `$generated@@103` is the guard/fact injected by the call ensures.
- `$generated@@105` is the assertion fact.

## 4) Unsat Core Extraction

Command run in this folder:
- `z3 output.smt2.1`

Observed output:

```text
unsat
(:rlimit 4334)
(aux$$assume$$id1$id5$ensures aux$$assert$$id7)
```

So the unsat core is exactly:
- `aux$$assume$$id1$id5$ensures`
- `aux$$assert$$id7`

## 5) Unsat Core -> Source-Level Explanation

### Core atom A: aux$$assume$$id1$id5$ensures
Back-mapping:
- `id1` comes from call-level postcondition of `ret32`: `x == 32`.
- `id5` comes from Main's call site `ret32(5)`.

Meaning:
- "From this call, the callee postcondition is available here."

### Core atom B: aux$$assert$$id7
Back-mapping:
- `id7` is Main's `assert n==32`.

Meaning:
- This is the goal being discharged in Main.
