import { ProofGraph } from "./proof-graph.js";
import { Node, TopNode, CallNode, classifyNodeType } from "./node.js";
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
      //   file(line,col): message
      const entryMatch = line.match(/\s+(.+?)\((\d+),(\d+)\)(?:\s*-\s*\((\d+),(\d+)\))?:\s+(.+)/);
      if (!entryMatch) continue;

      const file = entryMatch[1].trim();
      const startLine = parseInt(entryMatch[2], 10);
      const startCol = parseInt(entryMatch[3], 10);
      const endLine = entryMatch[4] ? parseInt(entryMatch[4], 10) : startLine;
      const endCol = entryMatch[5] ? parseInt(entryMatch[5], 10) : startCol;
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
    const nodeCache = new Map<string, Node>();

    const parseClauseTarget = (proofText: string): {
      kind: "requires" | "ensures";
      file: string;
      startLine: number;
      startCol: number;
      endLine: number;
      endCol: number;
    } | null => {
      const m = proofText.match(/(requires|ensures) clause at\s+(.+?)\((\d+),(\d+)\)(?:\s*-\s*\((\d+),(\d+)\))?/);
      if (!m) return null;
      const kind = m[1] as "requires" | "ensures";
      const file = m[2].trim();
      const startLine = parseInt(m[3], 10);
      const startCol = parseInt(m[4], 10);
      const endLine = m[5] ? parseInt(m[5], 10) : startLine;
      const endCol = m[6] ? parseInt(m[6], 10) : startCol;
      return { kind, file, startLine, startCol, endLine, endCol };
    };

    const getOrCreateNode = (batch: ParsedBatch, info: ParsedBatch["topAssertion"]): Node => {
      const inferredType = classifyNodeType(info.proofText, false);
      const span = `${info.startLine},${info.startCol}-${info.endLine},${info.endCol}`;
      const key = `${info.file}|${batch.methodName}|${batch.methodType}|${span}|${inferredType}`;

      const existing = nodeCache.get(key);
      if (existing) return existing;

      let node: Node;
      if (inferredType === TokenType.Call) {
        node = new CallNode(
          info.file,
          info.startLine,
          info.startCol,
          info.endLine,
          info.endCol,
          info.proofText,
          batch.methodName,
          false,
          batch.methodType
        );
      } else {
        node = new Node(
          info.file,
          info.startLine,
          info.startCol,
          info.endLine,
          info.endCol,
          info.proofText,
          batch.methodName,
          false,
          batch.methodType
        );
      }

      nodeCache.set(key, node);
      return node;
    };

    for (const batch of batches) {
      const topInfo = batch.topAssertion;
      const topNode = new TopNode(
        topInfo.file,
        topInfo.startLine,
        topInfo.startCol,
        topInfo.endLine,
        topInfo.endCol,
        topInfo.proofText,
        batch.methodName,
        batch.methodType
      );

      (topNode as any).batchIndex = batch.batchIndex;
      (topNode as any).batchOutcome = batch.outcome;
      (topNode as any).batchDuration = batch.duration;
      (topNode as any).batchResourceCount = batch.resourceCount;
      (topNode as any).methodType = batch.methodType;

      graph.addTopNode(topNode);

      for (const provedInfo of batch.provedBy) {
        const provedNode = getOrCreateNode(batch, provedInfo);
        graph.addNode(provedNode);
        graph.addProvedBy(topNode.getId(), provedNode.getId());

        if (provedNode instanceof CallNode) {
          const target = parseClauseTarget(provedInfo.proofText);
          if (target) {
            const targetNode = new Node(
              target.file,
              target.startLine,
              target.startCol,
              target.endLine,
              target.endCol,
              `${target.kind} clause`,
              batch.methodName,
              false,
              batch.methodType
            );
            graph.addNode(targetNode);
            graph.connectCall(provedNode.getId(), targetNode.getId());
          }
        }
      }

      for (const unusedInfo of batch.unusedBy) {
        const unusedNode = getOrCreateNode(batch, unusedInfo);
        graph.addNode(unusedNode);
        graph.markProofUnused(topNode.getId(), unusedNode.getId());

        if (unusedNode instanceof CallNode) {
          const target = parseClauseTarget(unusedInfo.proofText);
          if (target) {
            const targetNode = new Node(
              target.file,
              target.startLine,
              target.startCol,
              target.endLine,
              target.endCol,
              `${target.kind} clause`,
              batch.methodName,
              false,
              batch.methodType
            );
            graph.addNode(targetNode);
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
