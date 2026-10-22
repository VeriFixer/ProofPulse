import { CovStatus } from "./types.js";
import { ProofGraph } from "./proof-graph.js";
import { applyCoverage, computeLineStatus } from "./coverage.js";
import type { CoverageReport } from "./report/coverage-report.js";
import { dafnyLogToReport } from "./backends/dafny/log-parser.js";

/**
 * Proof: the main entry point for analyzing a coverage report.
 * Pipeline: report → build graph → apply coverage → compute line status.
 */
export class Proof {
  proofGraph: ProofGraph;
  lineStatus: CovStatus[];

  constructor(report: CoverageReport, sourceCode: string) {
    // Step 1: Build graph from the report
    this.proofGraph = ProofGraph.fromReport(report);

    // Step 2: Apply coverage (internal + semantic passes)
    applyCoverage(this.proofGraph);

    // Step 3: Compute per-line status
    this.lineStatus = computeLineStatus(this.proofGraph, sourceCode);
  }
}

/** Analyze a coverage report produced by any backend. */
export function analyzeReport(sourceCode: string, report: CoverageReport): Proof {
  return new Proof(report, sourceCode);
}

/** Dafny convenience: analyze a Dafny text verification log. */
export function parseProof(dafnyCode: string, proofLog: string): Proof {
  return new Proof(dafnyLogToReport(proofLog), dafnyCode);
}
