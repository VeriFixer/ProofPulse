# Debug: Single-File Evaluation

## Prerequisites

Custom Dafny path:
```
/home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny
```

## 1. Run ProofPulse (coverage/classification with YAML output)

Runs Dafny verification, builds proof graph, dumps YAML, and shows step-by-step classification reasoning.

```bash
npx tsx --no-warnings evaluation/src/debug-single.ts <file.dfy> \
  --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny \
  --timeout 120
```

Example:
```bash
npx tsx --no-warnings evaluation/src/debug-single.ts .eval-tmp/RQ2-GPT4/task_id_14.dfy \
  --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny
```

Output includes:
- Full YAML proof graph (nodes, edges, coverage statuses)
- Postcondition classification steps (which CodeLine deps are covered/uncovered)
- Invariant classification steps (same logic)
- Precondition classification steps (filtering out well-formedness)
- Overall strong/weak result

## 2. Run Evaluation Benchmark (single dataset, verbose)

Runs the full benchmark pipeline on a dataset with per-file verbose output.

```bash
npx tsx --no-warnings evaluation/src/cli.ts \
  --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny \
  --verbose \
  --dataset RQ3-GPT4
```

### With unsat core minimization:
```bash
npx tsx --no-warnings evaluation/src/cli.ts \
  --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny \
  --verbose \
  --force-core-minimization \
  --dataset RQ3-GPT4
```

### Compare minimization vs baseline:
```bash
npx tsx --no-warnings evaluation/src/cli.ts \
  --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny \
  --compare-minimization \
  --dataset RQ3-GPT4
```

## 3. Available datasets

- `RQ1-GPT4`, `RQ1-PaLM2`
- `RQ2-GPT4`, `RQ2-PaLM2`
- `RQ3-GPT4`, `RQ3-PaLM2`
- `all`

## 4. Classification semantics (current)

- **Postcondition/Invariant**: For each correctness-type top, collect `provedBy ∪ proofUnused` nodes. Only check `CodeLine` typed nodes. If any CodeLine dep is `Uncovered` → weak. Well-formedness tops are always strong.
- **Precondition**: Only consider correctness methodType nodes. All covered → required, any uncovered → optional.
- **Overall**: strong iff postcondition is strong.
