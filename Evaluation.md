# Evaluation

## Prerequisites

- **Dafny** installed and on PATH (or specify `--dafny-path`)
- **Node.js** ≥ 18
- `git submodule update --init` (pulls `dafny-synthesis` dataset)
- `npm install` at repo root (installs workspaces)

## Running the Benchmark

```bash
# Single dataset (default: RQ3-GPT4)
npx tsx evaluation/src/cli.ts

# Specific dataset
npx tsx evaluation/src/cli.ts --dataset RQ1-GPT4

# All datasets
npx tsx evaluation/src/cli.ts --dataset all

# With unsat-core minimization
npx tsx evaluation/src/cli.ts --dataset all --force-core-minimization

# Compare baseline vs minimized
npx tsx evaluation/src/cli.ts --dataset all --compare-minimization
```

### Using a Custom Dafny Binary

The default Dafny binary may have bugs (e.g. untracked assignments). Use `--dafny-path` to point to a patched build:

```bash
# Using the ProofPulse custom Dafny (recommended)
# With unsat-core minimization
npx tsx evaluation/src/cli.ts --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny --dataset all --force-core-minimization

# Or put it on PATH instead
PATH="/home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries:$PATH" npx tsx evaluation/src/cli.ts --dataset all
```

The custom binary at `/home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny` fixes the untracked assignments bug and produces correct proof logs for scoped coverage classification.

### Options

| Flag | Default | Description |
|------|---------|-------------|
| `--repo-root <path>` | `dafny-synthesis` | Path to dafny-synthesis submodule |
| `--dafny-path <path>` | `dafny` | Dafny binary |
| `--timeout <sec>` | `60` | Per-file verification timeout |
| `--output <path>` | `evaluation/results/benchmark-results.json` | Output JSON |
| `--dataset <id>` | `RQ3-GPT4` | Dataset or `all` |
| `--concurrency <n>` | CPUs - 1 | Parallel workers |
| `--verbose` | off | Print per-file details (forces sequential) |
| `--interactive` | off | Step-through mode |
| `--force-core-minimization` | off | Enable unsat core minimization |
| `--compare-minimization` | off | Run baseline + minimized, report diffs |

## What to Expect

### Output Files

| File | Description |
|------|-------------|
| `evaluation/results/benchmark-results.json` | Full results with per-file classifications |
| `evaluation/results/benchmark-results-{dataset}.json` | Per-dataset results (when `--dataset all`) |
| `evaluation/results/*-comparison.json` | Baseline vs minimized diffs |
| `evaluation/results/*-aggregate-tables.tex` | LaTeX tables for paper |
| `.eval-tmp/logs/{dataset}/*.log.txt` | ProofPulse text reports per file |

### Console Output

The benchmark prints:
1. Progress counter (`[N/total] completed`)
2. Per-category confusion matrix (postconditions, preconditions, invariants)
3. Precision, recall, F1, accuracy per category
4. Summary line (processed / errors / skipped)

### Typical Runtime

- Single dataset (~50 files): 2–5 minutes depending on Dafny solver speed
- All 6 datasets: 15–30 minutes
- With `--compare-minimization`: doubles runtime (runs twice)

## Oracle Overrides

The oracle labels from the original dataset may be incorrect for the current Dafny version (e.g. `requires x != null` is no longer needed). The file `evaluation/oracle-overrides.json` is the single source of truth for oracle labels.

### Generating the overrides file

```bash
npx tsx evaluation/generate-oracle-overrides.ts
```

This reads all dataset oracle labels and produces `evaluation/oracle-overrides.json` with every task entry containing:
- `oracle` — the original label from the dataset (read-only reference)
- `override` — the effective label used for evaluation (edit this when you find errors)

Initially both are identical. When you find an oracle error, change only the `override` field.

### Example

```json
"RQ1-GPT4/276": {
  "oracle": { "precondition": "required" },
  "override": { "precondition": "optional" }
}
```

## Generating results.md

After the benchmark completes (and oracle-overrides.json exists), generate the results report:

```bash
npx tsx evaluation/generate-results-md.ts
```

This reads `evaluation/oracle-overrides.json` and benchmark results to produce `results.md`. When any override differs from the original oracle, the table shows `pred/oracle/overridden` format; otherwise just `pred/oracle`.

## Agent Divergence Classification

After running the benchmark and generating `results.md`, classify root causes of prediction errors using the headless Kiro CLI script.

### Prerequisites

- **Kiro CLI** installed and on PATH (`kiro-cli`)
- **`KIRO_API_KEY`** env var set (generate at https://app.kiro.dev/ → Settings → API Keys)
- Pro, Pro+, or Power subscription (required for headless mode)

### Running the Classification

```bash
# Default: qwen3-coder-next model, 4 parallel calls
./evaluation/run-classify-divergences.sh

# Custom concurrency and model
./evaluation/run-classify-divergences.sh --concurrency 15 --model qwen3-coder-next

# Use a stronger model for better schema adherence
./evaluation/run-classify-divergences.sh --concurrency 8 --model claude-haiku-4.5
```

| Flag | Default | Description |
|------|---------|-------------|
| `--concurrency N` | `4` | Parallel kiro-cli invocations |
| `--model MODEL` | `qwen3-coder-next` | Model to use (see `kiro-cli chat --list-models`) |

### How It Works

1. Reads `evaluation/results/divergence-analysis.json` (divergences from benchmark)
2. Generates one prompt per divergence containing the Dafny source + ProofPulse log + metadata
3. Calls `kiro-cli chat --no-interactive` for each — no tools, pure prompt → JSON response
4. Runs N calls in parallel as background jobs
5. Assembles all results into `evaluation/results/agent-classifications.json`
6. Generates `results_after_agent.md` report grouped by root cause

The agent config lives at `evaluation/agents/classify-divergence.json` with `"tools": []` (no tool access — all context is provided in the prompt).

### Cost

Qwen3 Coder Next is **0.05x** cost multiplier (cheapest available). 129 divergences ≈ 6–7 Auto-equivalent credits. Claude Haiku 4.5 at 0.4x would cost ~8x more but follows the output schema more strictly.

### Output Files

| File | Description |
|------|-------------|
| `evaluation/results/agent-classifications.json` | Structured JSON with all classifications |
| `results_after_analysis.md` | Markdown report grouped by root cause with links to source and logs |

### Generating the Report

After the classification script completes, generate the formatted report:

```bash
npx tsx evaluation/generate-results-after-analysis-md.ts
```

This reads `agent-classifications.json` and produces `results_after_analysis.md` with:
- Metadata (model used, date, counts)
- Summary table of root causes with percentages
- Detailed tables per root cause group with links to `.dfy` files and logs
- Collapsible explanations per group

### Root Cause Categories

| Category | Meaning |
|----------|---------|
| `quantifier_not_tracked` | Spec uses forall/exists that coverage can't track |
| `trivially_true_spec` | Vacuous postcondition appears strong but is meaningless |
| `oracle_error` | Oracle label is wrong, ProofPulse is correct |
| `multi_method` | Multiple methods cause coverage bleed |
| `tool_limitation` | Dafny/Z3 solver quirks |
| `insufficient_coverage_model` | Coverage model misses proof pattern |
| `other` | Doesn't fit above categories |

### Notes

- Weaker models (Qwen3 Coder Next) may produce free-form root cause labels instead of the strict 7 categories. Use a stronger model or post-process to normalize.
- The script errors out immediately if `KIRO_API_KEY` is not set.
- Temporary prompt/result files are stored in `.eval-tmp/classify-runs/`.

## Running Tests

```bash
# All evaluation tests (unit + property + integration)
npm test -w evaluation

# Property-based tests only
npx vitest --run src/__tests__/agent-helpers.property.test.ts --config evaluation/vitest.config.ts

# Unit tests only
npx vitest --run src/__tests__/agent-helpers.test.ts --config evaluation/vitest.config.ts
```

Tests validate the helper functions (path construction, validation, divergence identification, report generation, source truncation) with 100+ iterations of property-based testing via fast-check.
