# ProofPulse — Dafny Proof Coverage for VSCode

Analyses Dafny prover logs and shows proof coverage directly in the editor.

## Features

- **Gutter decorations** — red for uncovered lines, blue for CovTest
- **Inline decorations** — per-token coverage coloring
- **Hover diagnostics** — coverage status, proof text, type, and related dependency nodes
- **Run on save** — automatically re-analyses when you save a `.dfy` file
- **Command palette** — "ProofPulse: Run Coverage Analysis"

## Requirements

- [Dafny](https://github.com/dafny-lang/dafny) CLI must be installed and available in your PATH (or configured via `proofpulse.dafnyPath`)

## Settings

| Setting | Default | Description |
|---|---|---|
| `proofpulse.dafnyPath` | `"dafny"` | Path to the Dafny executable |
| `proofpulse.timeoutSeconds` | `60` | Verification timeout in seconds |
| `proofpulse.runOnSave` | `true` | Automatically run analysis when a `.dfy` file is saved |

## Usage

1. Open a `.dfy` file
2. Save the file (analysis runs automatically) or run "ProofPulse: Run Coverage Analysis" from the command palette
3. Hover over decorated tokens to see proof dependencies

## Coverage status

- **CovComplete** (green) — line/token is used in proving a postcondition
- **CovTest** (blue) — line/token is used in a proof but not tied to a postcondition
- **Uncovered** (red) — line/token is not used in any proof
