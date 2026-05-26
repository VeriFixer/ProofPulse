import { CovStatus } from "./types.js";
import { ProofGraph } from "./proof-graph.js";
import { DafnyReportParser } from "./dafny_report_parser.js";
import { applyCoverage, computeLineStatus } from "./coverage.js";

/**
 * Proof: the main entry point for analyzing a Dafny verification log.
 * Pipeline: parse log → build graph → apply coverage → compute line status.
 */
export class Proof {
  proofGraph: ProofGraph;
  lineStatus: CovStatus[];

  constructor(proofLog: string, sourceCode: string) {
    // Step 1: Parse log and build graph
    this.proofGraph = DafnyReportParser.parseAndBuild(proofLog);

    // Step 2: Apply coverage (internal + semantic passes)
    applyCoverage(this.proofGraph);

    // Step 3: Compute per-line status
    this.lineStatus = computeLineStatus(this.proofGraph, sourceCode);
  }
}

export function parseProof(dafnyCode: string, proofLog: string): Proof {
  return new Proof(proofLog, dafnyCode);
}
