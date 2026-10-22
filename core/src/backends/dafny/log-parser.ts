import { ProofGraph } from "../../proof-graph.js";
import { CoverageReport, QueryOutcome, UnitKind } from "../../report/coverage-report.js";
import { DafnyReportInfo, dafnyBatchesToReport } from "./adapter.js";
import { dafnyOutcome, dafnyUnitKind, parseDafnyDuration } from "./messages.js";

/** Section of an assertion batch the parser is currently reading. */
enum ParserSection {
  None = "none",
  Assertions = "assertions",
  ProvedBy = "provedBy",
  UnusedBy = "unusedBy",
}

export interface ParsedBatch {
  methodName: string;
  methodType: UnitKind;
  batchIndex: number;
  outcome: QueryOutcome;
  durationMs?: number;
  resourceCount: number;
  topAssertion: {
    file: string;
    startLine: number;
    startCol: number;
    endLine: number;
    endCol: number;
    proofText: string;
  };
  provedBy: Array<{
    file: string;
    startLine: number;
    startCol: number;
    endLine: number;
    endCol: number;
    proofText: string;
  }>;
  unusedBy: Array<{
    file: string;
    startLine: number;
    startCol: number;
    endLine: number;
    endCol: number;
    proofText: string;
  }>;
}

export class DafnyReportParser {
  /**
   * Parse a Dafny verification report and return structured batch data.
   */
  static parseBatches(logText: string, debug = false): ParsedBatch[] {
    const batches: ParsedBatch[] = [];
    const lines = logText.split("\n");

    let currentBatch: Partial<ParsedBatch> | null = null;
    let currentSection = ParserSection.None;
    let methodName = "";
    let methodType = UnitKind.Other;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];

      // "Results for Main (correctness)"
      const resultsMatch = line.match(/Results for\s+(.+?)\s*\(([^)]+)\)/);
      if (resultsMatch) {
        methodName = resultsMatch[1].trim();
        methodType = dafnyUnitKind(resultsMatch[2].trim());
        continue;
      }

      // "Assertion batch N:"
      const batchMatch = line.match(/\s+Assertion batch (\d+):/);
      if (batchMatch) {
        if (debug) console.log(`[DEBUG] Batch ${batchMatch[1]}`);
        if (currentBatch && currentBatch.topAssertion) {
          batches.push(currentBatch as ParsedBatch);
        }

        const batchIndex = parseInt(batchMatch[1], 10);
        currentBatch = {
          methodName,
          methodType,
          batchIndex,
          provedBy: [],
          unusedBy: [],
        };
        currentSection = ParserSection.None;
        continue;
      }

      if (!currentBatch) continue;

      const outcomeMatch = line.match(/\s+Outcome:\s+(.+)/);
      if (outcomeMatch) {
        currentBatch.outcome = dafnyOutcome(outcomeMatch[1].trim());
        continue;
      }

      const durationMatch = line.match(/\s+Duration:\s+(.+)/);
      if (durationMatch) {
        currentBatch.durationMs = parseDafnyDuration(durationMatch[1]);
        continue;
      }

      const resourceMatch = line.match(/\s+Resource count:\s+(\d+)/);
      if (resourceMatch) {
        currentBatch.resourceCount = parseInt(resourceMatch[1], 10);
        continue;
      }

      // Section markers
      if (line.includes("Assertions:")) {
        currentSection = ParserSection.Assertions;
        continue;
      }
      if (line.includes("Proof dependencies:")) {
        currentSection = ParserSection.ProvedBy;
        continue;
      }
      if (line.includes("Unused by proof:")) {
        currentSection = ParserSection.UnusedBy;
        continue;
      }

      // Common entry line format:
      //   file(line,col)-(line,col): message
      const entryMatch = line.match(/\s+(.+?)\((\d+),(\d+)\)\s*-\s*\((\d+),(\d+)\):\s+(.+)/);
      if (!entryMatch) {
        // Detect point-only format and reject it
        const pointMatch = line.match(/\s+(.+?)\((\d+),(\d+)\):\s+(.+)/);
        if (pointMatch) {
          throw new Error("Point location not supported — requires full range format");
        }
        continue;
      }

      const file = entryMatch[1].trim();
      const startLine = parseInt(entryMatch[2], 10);
      const startCol = parseInt(entryMatch[3], 10);
      const endLine = parseInt(entryMatch[4], 10);
      const endCol = parseInt(entryMatch[5], 10);
      const proofText = entryMatch[6].trim();

      if (currentSection === ParserSection.Assertions) {
        currentBatch.topAssertion = { file, startLine, startCol, endLine, endCol, proofText };
      } else if (currentSection === ParserSection.ProvedBy) {
        currentBatch.provedBy!.push({ file, startLine, startCol, endLine, endCol, proofText });
      } else if (currentSection === ParserSection.UnusedBy) {
        currentBatch.unusedBy!.push({ file, startLine, startCol, endLine, endCol, proofText });
      }
    }

    if (currentBatch && currentBatch.topAssertion) {
      batches.push(currentBatch as ParsedBatch);
    }

    return batches;
  }

  /**
   * Parse a Dafny report and build the graph in one go.
   */
  static parseAndBuild(logText: string, debug = false): ProofGraph {
    return ProofGraph.fromReport(dafnyBatchesToReport(this.parseBatches(logText, debug)));
  }
}

/** Parse a Dafny text log straight into a coverage report. */
export function dafnyLogToReport(log: string, info: DafnyReportInfo = {}): CoverageReport {
  return dafnyBatchesToReport(DafnyReportParser.parseBatches(log), info);
}
