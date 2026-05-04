# ProofPulse — Dafny Proof Coverage for VSCode

Analyses Dafny prover logs and shows proof coverage directly in the editor.

## Features

- **Gutter decorations** — red for uncovered lines, blue for CovTest
- **Inline decorations** — per-token coverage coloring
- **Hover diagnostics** — coverage status, proof text, type, and related dependency nodes
- **Run on save** — automatically re-analyses when you save a `.dfy` file
- **Command palette** — "ProofPulse: Run Coverage Analysis"
- **Get Proof Report** — right-click a `.dfy` file in the editor or explorer to launch an interactive coverage report in the browser

## Requirements

- [Dafny](https://github.com/dafny-lang/dafny) CLI must be installed and available in your PATH (or configured via `proofpulse.dafnyPath`)
- [Python 3](https://www.python.org/) must be available as `python` on PATH (or configured via `proofpulse.pythonPath`) — required only when `forceMinimization` is enabled

## Settings

| Setting | Default | Description |
|---|---|---|
| `proofpulse.dafnyPath` | `"dafny"` | Path to the Dafny executable |
| `proofpulse.pythonPath` | `"python"` | Path to the Python interpreter (needed for Z3 unsat core minimization) |
| `proofpulse.timeoutSeconds` | `60` | Verification timeout in seconds |
| `proofpulse.runOnSave` | `true` | Automatically run analysis when a `.dfy` file is saved |
| `proofpulse.forceMinimization` | `true` | Enable unsat core minimization for Z3 solver calls. Uses an interactive z3 wrapper that intercepts solver queries and minimizes unsat cores. Slower but produces tighter proof dependencies. Requires Python on PATH (or configured via `proofpulse.pythonPath`). |
| `proofpulse.decorationOpacity` | `0.08` | Opacity for line background decorations (`0.0`–`0.5`). Higher values make coverage highlights more visible. |

## Usage

1. Open a `.dfy` file
2. Save the file (analysis runs automatically) or run "ProofPulse: Run Coverage Analysis" from the command palette
3. Hover over decorated tokens to see proof dependencies

## Get Proof Report (Context Menu)

Right-click any `.dfy` file — in the editor tab or the explorer tree — and select **"ProofPulse: Get Proof Report"**.

This launches the web viewer server targeting that file, runs Dafny verification, and opens the coverage graph in your browser. No need to leave VSCode.

The menu entry only appears for `.dfy` files.

## Coverage status

- **CovComplete** (green) — line/token is used in proving a postcondition
- **CovTest** (blue) — line/token is used in a proof but not tied to a postcondition
- **Uncovered** (red) — line/token is not used in any proof
