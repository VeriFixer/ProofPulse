# Implementation Plan: ProofPulse VSCode Extension

## Overview

Monorepo conversion: JS→TS. Extract `@proofpulse/core`, build VSCode extension, refactor web API. Incremental: core types → parser → coverage → extension → server refactor.

## Tasks

- [x] 1. Set up monorepo and build infrastructure
  - [x] 1.1 Create root workspace config
    - Add `"workspaces": ["packages/*"]` to root `package.json`
    - Create `packages/core/package.json` with name `@proofpulse/core`, ES module, strict TS
    - Create `packages/vscode-extension/package.json` with VSCode extension manifest, commands, configuration contributes
    - _Requirements: 1.1, 1.2, 9.1, 10.1, 10.2_

  - [x] 1.2 Create tsconfig files
    - `packages/core/tsconfig.json`: strict, ES2022, ESNext modules, declaration emit
    - `packages/vscode-extension/tsconfig.json`: strict, ES2022, CommonJS, references core
    - _Requirements: 1.1_

  - [x] 1.3 Set up test infrastructure
    - Add vitest or node:test + fast-check to core devDependencies
    - Add esbuild config for extension bundling
    - _Requirements: 1.1_

- [x] 2. Implement core types and Node class
  - [x] 2.1 Create `packages/core/src/types.ts`
    - Define CovStatus, TokenType enums, SourceLocation, NodeData, DafnyResult, DafnyOptions interfaces
    - _Requirements: 1.2, 1.3_

  - [x] 2.2 Create `packages/core/src/node.ts`
    - Port Node class from `spans_provider.js` to TypeScript
    - Constructor, updateIsTopAssertion heuristic, connectTo, toJSON, fromJSON
    - _Requirements: 1.3, 3.2_

  - [x] 2.3 Write property test: TokenType heuristic (Property 3)
    - **Property 3: TokenType assignment matches heuristic**
    - **Validates: Requirements 3.2**

- [x] 3. Implement ProofGraph and serialization
  - [x] 3.1 Create `packages/core/src/proof-graph.ts`
    - Port ProofGraph class: nodes/topNodes maps, addNode, addEdge, getBFSNeighbors, toJSON, fromJSON
    - _Requirements: 1.3, 3.1, 3.5, 4.2_

  - [x] 3.2 Create `packages/core/src/serialization.ts`
    - serializeProofGraph (canonical JSON), deserializeProofGraph
    - _Requirements: 3.6, 3.7_

  - [x] 3.3 Write property test: JSON round-trip (Property 1)
    - **Property 1: ProofGraph JSON round-trip**
    - **Validates: Requirements 1.4, 3.7**

  - [ ]* 3.4 Write property test: structurally valid graph (Property 2)
    - **Property 2: Log parsing produces structurally valid graph**
    - **Validates: Requirements 3.1, 3.5**

  - [ ]* 3.5 Write property test: BFS neighbors (Property 7)
    - **Property 7: BFS neighbors match transitive closure**
    - **Validates: Requirements 4.2**

- [x] 4. Checkpoint
  - Ensure all tests pass, ask the user if questions arise.

- [x] 5. Implement Proof parser and coverage
  - [x] 5.1 Create `packages/core/src/proof.ts`
    - Port Proof class: log parsing (assertion batches, proof deps, unused), setCoverageStatus, setLineStatus
    - Export `parseProof(dafnyCode, proofLog): Proof`
    - _Requirements: 3.1, 3.2, 3.3, 3.4_

  - [x] 5.2 Create `packages/core/src/coverage.ts`
    - computeLineStatus, getNodesByLine, getRelatedNodes, getNodeInfo
    - _Requirements: 4.1, 4.2, 4.3, 4.4_

  - [x] 5.3 Write property test: CovStatusInternal BFS reachability (Property 4)
    - **Property 4: CovStatusInternal follows BFS reachability from top assertions**
    - **Validates: Requirements 3.3**

  - [x] 5.4 Write property test: CovStatus token-class policies (Property 5)
    - **Property 5: CovStatus follows token-class policies**
    - **Validates: Requirements 3.4**

  - [x] 5.5 Write property test: line status worst-case (Property 6)
    - **Property 6: Line status is worst-case of token statuses**
    - **Validates: Requirements 4.1**

  - [x] 5.6 Write property test: getNodesByLine span containment (Property 8)
    - **Property 8: getNodesByLine returns exactly span-containing nodes**
    - **Validates: Requirements 4.4**

- [x] 6. Implement Dafny runner and core barrel
  - [x] 6.1 Create `packages/core/src/dafny-runner.ts`
    - Spawn dafny verify with coverage/log flags, temp dir management, timeout handling
    - Return DafnyResult with log, exitCode, timedOut, error
    - _Requirements: 2.1, 2.2, 2.3, 2.4_

  - [x] 6.2 Create `packages/core/src/index.ts`
    - Barrel export all public types, classes, functions
    - _Requirements: 1.2_

  - [ ]* 6.3 Write unit tests for dafny-runner
    - Test error cases: not found, timeout, non-zero exit
    - _Requirements: 2.2, 2.3, 2.4_

- [x] 7. Checkpoint
  - Ensure all tests pass, ask the user if questions arise.

- [x] 8. Implement VSCode extension
  - [x] 8.1 Create `packages/vscode-extension/src/config.ts`
    - getDafnyPath(), getTimeout() reading VSCode settings
    - _Requirements: 10.1, 10.2, 10.3_

  - [x] 8.2 Create `packages/vscode-extension/src/decorations.ts`
    - Define gutter + inline decoration types (red uncovered, blue covTest)
    - applyDecorations(editor, lineStatus, nodes), clearDecorations(editor)
    - _Requirements: 6.1, 6.2, 6.3, 6.4, 7.1, 7.2, 7.3_

  - [x] 8.3 Create `packages/vscode-extension/src/hover.ts`
    - ProofPulseHoverProvider: lookup nodes at position, format tooltip with status, prooftext, location, type, BFS neighbors
    - _Requirements: 8.1, 8.2, 8.3_

  - [x] 8.4 Create `packages/vscode-extension/src/commands.ts`
    - registerRunAnalysis: validate .dfy, show progress, call runDafny → parseProof → applyDecorations, register hover, handle errors
    - _Requirements: 9.1, 9.2, 9.3, 9.4, 9.5_

  - [x] 8.5 Create `packages/vscode-extension/src/extension.ts`
    - activate: register command, hover provider, document change listener to clear stale decorations
    - deactivate: cleanup
    - _Requirements: 6.4, 9.1_

  - [x] 8.6 Write property test: gutter decorations match line status (Property 9)
    - **Property 9: Gutter decorations match line status**
    - **Validates: Requirements 6.1, 6.2, 6.3**

  - [x] 8.7 Write property test: inline decorations match node status (Property 10)
    - **Property 10: Inline decorations match node status**
    - **Validates: Requirements 7.1, 7.2, 7.3**

  - [x] 8.8 Write property test: hover content completeness (Property 11)
    - **Property 11: Hover content contains all required node info and neighbors**
    - **Validates: Requirements 8.1, 8.2**

- [x] 9. Checkpoint
  - Ensure all tests pass, ask the user if questions arise.

- [x] 10. Refactor web API to consume core
  - [x] 10.1 Refactor `src/server.ts`
    - Import @proofpulse/core for log parsing, graph construction, Dafny execution
    - Replace inline spans_provider.js usage
    - Preserve all existing HTTP routes and response formats
    - _Requirements: 5.1, 5.2, 5.3_

  - [x] 10.2 Write integration tests for web API
    - Verify routes return same response formats after refactor
    - Test /api/run uses core's Dafny execution
    - _Requirements: 5.2, 5.3_

- [x] 11. Final checkpoint
  - Ensure all tests pass, ask the user if questions arise.

## Notes

- Tasks marked with `*` are optional and can be skipped for faster MVP
- Each property test maps to a specific correctness property from the design document
- TypeScript strict mode throughout; esbuild bundles the extension
