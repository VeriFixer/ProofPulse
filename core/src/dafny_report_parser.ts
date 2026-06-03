import { ProofGraph } from "./proof-graph.js";
import { classifyNodeType } from "./proof-node.js";
import { TokenType } from "./types.js";

export interface ParsedBatch {
  methodName: string;
  methodType: string; // e.g. "correctness", "well-formedness"
  batchIndex: number;
  outcome: string;
  duration: string;
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
    let currentSection: "none" | "assertions" | "provedBy" | "unusedBy" = "none";
    let methodName = "";
    let methodType = "";

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];

      // "Results for Main (correctness)"
      const resultsMatch = line.match(/Results for\s+(.+?)\s*\(([^)]+)\)/);
      if (resultsMatch) {
        methodName = resultsMatch[1].trim();
        methodType = resultsMatch[2].trim();
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
        currentSection = "none";
        continue;
      }

      if (!currentBatch) continue;

      const outcomeMatch = line.match(/\s+Outcome:\s+(.+)/);
      if (outcomeMatch) {
        currentBatch.outcome = outcomeMatch[1].trim();
        continue;
      }

      const durationMatch = line.match(/\s+Duration:\s+(.+)/);
      if (durationMatch) {
        currentBatch.duration = durationMatch[1].trim();
        continue;
      }

      const resourceMatch = line.match(/\s+Resource count:\s+(\d+)/);
      if (resourceMatch) {
        currentBatch.resourceCount = parseInt(resourceMatch[1], 10);
        continue;
      }

      // Section markers
      if (line.includes("Assertions:")) {
        currentSection = "assertions";
        continue;
      }
      if (line.includes("Proof dependencies:")) {
        currentSection = "provedBy";
        continue;
      }
      if (line.includes("Unused by proof:")) {
        currentSection = "unusedBy";
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

      if (currentSection === "assertions") {
        currentBatch.topAssertion = { file, startLine, startCol, endLine, endCol, proofText };
      } else if (currentSection === "provedBy") {
        currentBatch.provedBy!.push({ file, startLine, startCol, endLine, endCol, proofText });
      } else if (currentSection === "unusedBy") {
        currentBatch.unusedBy!.push({ file, startLine, startCol, endLine, endCol, proofText });
      }
    }

    if (currentBatch && currentBatch.topAssertion) {
      batches.push(currentBatch as ParsedBatch);
    }

    return batches;
  }

  /**
   * Convert parsed batches into a ProofGraph.
   */
  static buildProofGraph(batches: ParsedBatch[], debug = false): ProofGraph {
    const graph = new ProofGraph();

    const parseClauseTarget = (proofText: string): {
      kind: "requires" | "ensures";
      file: string;
      startLine: number;
      startCol: number;
      endLine: number;
      endCol: number;
    } | null => {
      const m = proofText.match(/(requires|ensures) clause at\s+(.+?)\((\d+),(\d+)\)\s*-\s*\((\d+),(\d+)\)/);
      if (!m) return null;
      const kind = m[1] as "requires" | "ensures";
      const file = m[2].trim();
      const startLine = parseInt(m[3], 10);
      const startCol = parseInt(m[4], 10);
      const endLine = parseInt(m[5], 10);
      const endCol = parseInt(m[6], 10);
      return { kind, file, startLine, startCol, endLine, endCol };
    };

    for (const batch of batches) {
      // Skip well-formedness batches — only correctness is relevant
      if (batch.methodType !== "correctness") continue;

      const topInfo = batch.topAssertion;

      // Top assertion node
      const topNode = graph.getOrCreate(
        topInfo.file,
        { line: topInfo.startLine, col: topInfo.startCol },
        { line: topInfo.endLine, col: topInfo.endCol },
        batch.methodName,
        batch.methodType,
        topInfo.proofText,
      );
      topNode.addRole("isTop");
      topNode.topMeta = {
        batchIndex: batch.batchIndex,
        batchOutcome: batch.outcome,
        batchDuration: batch.duration,
        batchResourceCount: batch.resourceCount,
      };

      // Proof dependencies
      for (const provedInfo of batch.provedBy) {
        const provedNode = graph.getOrCreate(
          provedInfo.file,
          { line: provedInfo.startLine, col: provedInfo.startCol },
          { line: provedInfo.endLine, col: provedInfo.endCol },
          batch.methodName,
          batch.methodType,
          provedInfo.proofText,
        );
        provedNode.addRole("isProvedBy");

        if (classifyNodeType([provedInfo.proofText], false) === TokenType.Call) {
          provedNode.addRole("isCall");
        }

        graph.addProvedBy(topNode.getId(), provedNode.getId());

        // Call clause target
        if (provedNode.roles.isCall) {
          const target = parseClauseTarget(provedInfo.proofText);
          if (target) {
            const targetNode = graph.getOrCreate(
              target.file,
              { line: target.startLine, col: target.startCol },
              { line: target.endLine, col: target.endCol },
              batch.methodName,
              batch.methodType,
              `${target.kind} clause`,
            );
            graph.connectCall(provedNode.getId(), targetNode.getId());
          }
        }
      }

      // Unused by proof
      for (const unusedInfo of batch.unusedBy) {
        const unusedNode = graph.getOrCreate(
          unusedInfo.file,
          { line: unusedInfo.startLine, col: unusedInfo.startCol },
          { line: unusedInfo.endLine, col: unusedInfo.endCol },
          batch.methodName,
          batch.methodType,
          unusedInfo.proofText,
        );
        unusedNode.addRole("isUnused");

        if (classifyNodeType([unusedInfo.proofText], false) === TokenType.Call) {
          unusedNode.addRole("isCall");
        }

        graph.markProofUnused(topNode.getId(), unusedNode.getId());

        // Call clause target
        if (unusedNode.roles.isCall) {
          const target = parseClauseTarget(unusedInfo.proofText);
          if (target) {
            const targetNode = graph.getOrCreate(
              target.file,
              { line: target.startLine, col: target.startCol },
              { line: target.endLine, col: target.endCol },
              batch.methodName,
              batch.methodType,
              `${target.kind} clause`,
            );
            graph.connectCall(unusedNode.getId(), targetNode.getId());
          }
        }
      }

      if (debug) {
        console.log(`[DEBUG] Batch ${batch.batchIndex}: top=${topNode.getId()} provedBy=${batch.provedBy.length} unusedBy=${batch.unusedBy.length}`);
      }
    }

    return graph;
  }

  /**
   * Parse a Dafny report and build the graph in one go.
   */
  static parseAndBuild(logText: string, debug = false): ProofGraph {
    const batches = this.parseBatches(logText, debug);
    return this.buildProofGraph(batches, debug);
  }
}
