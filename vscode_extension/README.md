# ProofPulse — Dafny Proof Coverage for VSCode

Analyses Dafny prover logs and shows proof coverage directly in the editor.

## Features

- **Gutter decorations** — red for uncovered lines, yellow for CovTest
- **Hover diagnostics** — coverage status, proof text, type, and related dependency nodes
- **Run on save** — automatically re-analyses when you save a `.dfy` file
- **Command palette** — "ProofPulse: Run Coverage Analysis"
- **Get Proof Report** — right-click a `.dfy` file in the editor or explorer to launch an interactive coverage report in the browser

## Requirements

- [Dafny](https://github.com/dafny-lang/dafny) — either the official [Dafny VS Code extension](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode) (recommended) or the Dafny CLI in PATH

No other external dependencies. The minimization pipeline is pure TypeScript/Node.js.

## Dependency Resolution

ProofPulse needs a Dafny binary and (when minimization is enabled) a compatible Z3 binary. To avoid version mismatches, resolution follows this priority:

**Dafny:** user override (`proofpulse.dafnyPath`) → bundled Dafny VS Code extension → PATH

**Z3:** user override (`proofpulse.z3Path`) → sibling z3 of resolved Dafny → bundled Dafny VS Code extension → PATH (with compatibility warning)

The safest setup is having the official Dafny VS Code extension installed — ProofPulse will find both Dafny and its matching Z3 automatically. If Z3 is only found on PATH (not paired with the resolved Dafny), a warning is logged to the ProofPulse output channel since the versions may be incompatible.

If problemns persist manually configuration of paths to dafny and a compatible z3 binary must me configured.

## Settings

| Setting | Default | Description |
|---|---|---|
| `proofpulse.dafnyPath` | `"dafny"` | Path to the Dafny executable. Leave at default to auto-resolve from the Dafny VS Code extension bundle, then PATH. |
| `proofpulse.z3Path` | `""` | Path to the Z3 binary (for core minimization). Leave empty to auto-resolve from the Dafny installation. |
| `proofpulse.timeoutSeconds` | `60` | Verification timeout in seconds |
| `proofpulse.runOnSave` | `true` | Automatically run analysis when a `.dfy` file is saved |
| `proofpulse.forceMinimization` | `false` | **Experimental.** Enable unsat core minimization. Intercepts Z3 solver queries and minimizes unsat cores for tighter proof dependencies. Slower but more precise. Tested on Linux (Nobara/Fedora); not known if well supported on other platforms. |
| `proofpulse.decorationOpacity` | `0.08` | Opacity for line background decorations (`0.0`–`0.5`). Higher values make coverage highlights more visible. |

## Usage

1. Open a `.dfy` file
2. Save the file (analysis runs automatically) or run "ProofPulse: Run Coverage Analysis" from the command palette
3. Hover over decorated tokens to see proof dependencies

## Get Proof Report (Context Menu)

Right-click any  marked uncovered/CovTest line on the `.dfy` file — in the editor tab or the explorer tree — and select **"ProofPulse: Get Proof Report"**.

This launches the web viewer server targeting that file, runs Dafny verification, and opens the coverage graph in your browser. No need to leave VSCode.

The menu entry only appears for `.dfy` files.

## Coverage status

- **CovComplete** (green) — line/token is used in proving a postcondition
- **CovTest** (blue) — line/token is used in a proof but not tied to a postcondition
- **Uncovered** (red) — line/token is not used in any proof
