# Requirements Document

## Introduction

Convert ProofPulse from JavaScript to TypeScript. Extract a shared core library (Dafny runner, log parser, proof graph, coverage queries). Build a VSCode extension consuming that core to provide inline coverage decorations and hover diagnostics for `.dfy` files.

## Glossary

- **Core**: Shared TypeScript library containing Dafny execution, log parsing, proof graph construction, and coverage query functions.
- **Extension**: VSCode extension that consumes Core to display coverage in the editor.
- **ProofGraph**: Directed graph of proof dependency nodes parsed from Dafny prover logs.
- **Node**: A vertex in ProofGraph representing a source span with coverage status and token type.
- **CovStatus**: Coverage classification — CovComplete, CovTest, or Uncovered.
- **TokenType**: Classification of a Node — Postcondition, Precondition, AssertionManual, AssertionAutomatic, CodeLine.
- **Line_Status**: Per-line coverage derived as worst-case CovStatus of all tokens on that line.
- **Gutter_Decoration**: Colored icon in the VSCode editor gutter (left margin).
- **Hover_Diagnostic**: Tooltip shown when hovering over a token in VSCode, displaying dependency and status info.
- **Web_API**: Existing HTTP server (`src/server.js`) that will be refactored to consume Core.

## Requirements

### Requirement 1: TypeScript Conversion

**User Story:** As a developer, I want the codebase in TypeScript, so that both the web API and VSCode extension share type-safe code.

#### Acceptance Criteria

1. THE Core SHALL be written in TypeScript with strict mode enabled.
2. THE Core SHALL export all public types and functions as ES module exports.
3. THE Core SHALL preserve the existing semantics of Node, ProofGraph, Proof, CovStatus, TokenType, and coverage computation.
4. FOR ALL valid prover logs, parsing with the TypeScript Core then serializing the resulting ProofGraph to JSON then deserializing then re-serializing SHALL produce identical JSON (round-trip property).

### Requirement 2: Core — Dafny Execution

**User Story:** As a consumer of Core, I want to run Dafny verification on a `.dfy` file, so that I get a prover log for analysis.

#### Acceptance Criteria

1. WHEN a valid `.dfy` file path is provided, THE Core SHALL invoke `dafny verify` with coverage and log flags and return the prover log content.
2. WHEN Dafny is not found in PATH, THE Core SHALL return a descriptive error indicating Dafny is unavailable.
3. WHEN Dafny execution exceeds a configurable timeout, THE Core SHALL terminate the process and return a timeout error.
4. IF Dafny exits with a non-zero code, THEN THE Core SHALL still return the prover log content if available, along with the exit code.

### Requirement 3: Core — Log Parsing and Graph Construction

**User Story:** As a consumer of Core, I want to parse a prover log and build a proof graph, so that I can query coverage.

#### Acceptance Criteria

1. WHEN a prover log string is provided, THE Core SHALL parse assertion batches, proof dependencies, and unused sections into a ProofGraph.
2. THE Core SHALL assign TokenType to each Node using the existing heuristic rules.
3. THE Core SHALL compute CovStatusInternal for each Node via BFS from top assertions.
4. THE Core SHALL compute CovStatus for each Node by applying token-class policies (auto assertions forced covered, manual assertions downgraded if not CovComplete, postcondition alias/parent checks).
5. FOR ALL valid prover logs, THE Core log parser SHALL produce a ProofGraph where every edge references two existing nodes (no dangling edges).
6. THE Core SHALL provide a pretty-printer that serializes a ProofGraph to a canonical JSON format.
7. FOR ALL valid ProofGraph objects, parsing a log then pretty-printing then parsing the pretty-printed output SHALL produce an equivalent ProofGraph (round-trip property).

### Requirement 4: Core — Coverage Queries

**User Story:** As a consumer of Core, I want to query coverage per line and per element, so that I can render results in any UI.

#### Acceptance Criteria

1. WHEN a ProofGraph and source code string are provided, THE Core SHALL compute Line_Status as an array mapping each source line index to its CovStatus (worst-case of all tokens on that line).
2. WHEN a Node ID is provided, THE Core SHALL return the BFS neighbors (all related nodes) for that node.
3. WHEN a Node ID is provided, THE Core SHALL return the Node's CovStatus, CovStatusInternal, TokenType, proof text, and source location.
4. WHEN a line number is provided, THE Core SHALL return all Nodes whose source span includes that line.

### Requirement 5: Web API Refactor

**User Story:** As a developer, I want the web API to consume Core, so that logic is not duplicated.

#### Acceptance Criteria

1. THE Web_API SHALL import Core for log parsing, graph construction, and coverage queries instead of using `spans_provider.js` directly.
2. THE Web_API SHALL preserve all existing HTTP routes and response formats.
3. WHEN the Web_API receives a POST to `/api/run`, THE Web_API SHALL use Core's Dafny execution function.

### Requirement 6: VSCode Extension — Gutter Decorations

**User Story:** As a Dafny developer, I want colored gutter marks on my `.dfy` files, so that I see line-level coverage at a glance.

#### Acceptance Criteria

1. WHEN coverage analysis completes for a `.dfy` file, THE Extension SHALL display red Gutter_Decorations on lines with Line_Status equal to Uncovered.
2. WHEN coverage analysis completes for a `.dfy` file, THE Extension SHALL display blue Gutter_Decorations on lines with Line_Status equal to CovTest.
3. WHEN coverage analysis completes for a `.dfy` file, THE Extension SHALL display no special Gutter_Decoration on lines with Line_Status equal to CovComplete.
4. WHEN the user edits the `.dfy` file, THE Extension SHALL clear stale decorations until the next analysis run.

### Requirement 7: VSCode Extension — Element Decorations

**User Story:** As a Dafny developer, I want individual proof elements (assertions, postconditions, code spans) marked by coverage status, so that I see element-level detail.

#### Acceptance Criteria

1. WHEN coverage analysis completes, THE Extension SHALL apply red inline text decorations to tokens with CovStatus equal to Uncovered.
2. WHEN coverage analysis completes, THE Extension SHALL apply blue inline text decorations to tokens with CovStatus equal to CovTest.
3. WHEN coverage analysis completes, THE Extension SHALL apply no special inline decoration to tokens with CovStatus equal to CovComplete.

### Requirement 8: VSCode Extension — Hover Diagnostics

**User Story:** As a Dafny developer, I want to hover over a proof element and see its dependency info, so that I get the same insight as the web viewer's side panel.

#### Acceptance Criteria

1. WHEN the user hovers over a decorated token, THE Extension SHALL display a hover tooltip containing: CovStatus, proof text message, source location, TokenType, and CovStatusInternal.
2. WHEN the user hovers over a decorated token, THE Extension SHALL list all related nodes (BFS neighbors) with their IDs and proof text in the tooltip.
3. WHEN no coverage data exists for the hovered position, THE Extension SHALL display no tooltip.

### Requirement 9: VSCode Extension — Analysis Trigger

**User Story:** As a Dafny developer, I want to trigger coverage analysis from VSCode, so that I do not need the web UI.

#### Acceptance Criteria

1. THE Extension SHALL provide a command "ProofPulse: Run Coverage Analysis" that triggers Dafny verification and coverage computation on the active `.dfy` file.
2. WHEN the command is invoked, THE Extension SHALL show a progress indicator during Dafny execution.
3. WHEN analysis completes, THE Extension SHALL apply gutter decorations, element decorations, and register hover providers.
4. IF Dafny execution fails, THEN THE Extension SHALL display the error message in a VSCode notification.
5. IF no `.dfy` file is active, THEN THE Extension SHALL display a warning notification.

### Requirement 10: VSCode Extension — Configuration

**User Story:** As a Dafny developer, I want to configure the extension, so that it works with my environment.

#### Acceptance Criteria

1. THE Extension SHALL expose a `proofpulse.dafnyPath` setting defaulting to `"dafny"`.
2. THE Extension SHALL expose a `proofpulse.timeoutSeconds` setting defaulting to 60.
3. WHEN `proofpulse.dafnyPath` is set, THE Extension SHALL use that path to invoke Dafny instead of the default.
