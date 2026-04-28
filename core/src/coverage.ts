import { CovStatus, NodeData } from "./types.js";
import { Node } from "./node.js";
import { ProofGraph } from "./proof-graph.js";

/**
 * Compute per-line coverage status. Worst-case wins: Uncovered > CovTest > CovComplete.
 * Default is CovComplete for lines with no tokens.
 */
export function computeLineStatus(graph: ProofGraph, sourceCode: string): CovStatus[] {
  const lines = sourceCode.split("\n");
  const result: CovStatus[] = new Array(lines.length).fill(CovStatus.CovComplete);
  const nodes = graph.getAllNodes();

  for (const node of nodes) {
    if (!node || !node.start || !node.end) continue;
    const idx = Math.max(0, node.start.line - 1);
    if (idx >= result.length) continue;

    const current = result[idx];
    if (current === CovStatus.Uncovered) continue;

    if (node.covStatus === CovStatus.Uncovered) {
      result[idx] = CovStatus.Uncovered;
    } else if (node.covStatus === CovStatus.CovTest) {
      result[idx] = CovStatus.CovTest;
    }
  }

  return result;
}

/** Return all nodes whose source span includes the given line (1-based). */
export function getNodesByLine(graph: ProofGraph, line: number): Node[] {
  return graph.getAllNodes().filter(
    (n) => n.start.line <= line && line <= n.end.line,
  );
}

/** Return all BFS neighbors (both directions) for a node. null if nodeId not found. */
export function getRelatedNodes(graph: ProofGraph, nodeId: string): Node[] | null {
  const results = graph.getBFSNeighbors(nodeId, false, true);
  return results ? results.map((r) => r.node) : null;
}

/** Return serialized node data, or undefined if not found. */
export function getNodeInfo(graph: ProofGraph, nodeId: string): NodeData | undefined {
  const node = graph.getNode(nodeId);
  return node ? node.toJSON() : undefined;
}
