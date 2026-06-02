import { CovStatus } from "./types.js";
import { ProofGraph } from "./proof-graph.js";

export interface SpanNode {
  nodeId: string;
  startCol: number;
  endCol: number;
  compositeStatus: CovStatus;
  children: SpanNode[];
}

/**
 * Build a containment tree from flat spans on a single line.
 * Parent span ⊇ child span (by column range).
 */
export function buildSpanTree(
  nodesOnLine: Array<{ nodeId: string; startCol: number; endCol: number; compositeStatus: CovStatus }>,
): SpanNode[] {
  if (nodesOnLine.length === 0) return [];

  const sorted = [...nodesOnLine].sort((a, b) => {
    if (a.startCol !== b.startCol) return a.startCol - b.startCol;
    return (b.endCol - b.startCol) - (a.endCol - a.startCol);
  });

  const spanNodes: SpanNode[] = sorted.map((n) => ({
    nodeId: n.nodeId,
    startCol: n.startCol,
    endCol: n.endCol,
    compositeStatus: n.compositeStatus,
    children: [],
  }));

  const roots: SpanNode[] = [];
  for (const node of spanNodes) {
    if (!insertInto(roots, node)) {
      roots.push(node);
    }
  }

  return roots;
}

function insertInto(candidates: SpanNode[], node: SpanNode): boolean {
  for (const candidate of candidates) {
    if (contains(candidate, node)) {
      if (!insertInto(candidate.children, node)) {
        candidate.children.push(node);
      }
      return true;
    }
  }
  return false;
}

function contains(parent: SpanNode, child: SpanNode): boolean {
  return parent.startCol <= child.startCol && parent.endCol >= child.endCol &&
    !(parent.startCol === child.startCol && parent.endCol === child.endCol);
}

export function minStatus(a: CovStatus, b: CovStatus): CovStatus {
  const order: Record<CovStatus, number> = {
    [CovStatus.Uncovered]: 0,
    [CovStatus.CovTest]: 1,
    [CovStatus.CovComplete]: 2,
  };
  return order[a] <= order[b] ? a : b;
}

/**
 * Best-case status: CovComplete > CovTest > Uncovered.
 */
export function maxStatus(a: CovStatus, b: CovStatus): CovStatus {
  const order: Record<CovStatus, number> = {
    [CovStatus.Uncovered]: 0,
    [CovStatus.CovTest]: 1,
    [CovStatus.CovComplete]: 2,
  };
  return order[a] >= order[b] ? a : b;
}

/**
 * Compute line status from tree roots.
 * Line status = best-case (max) over root span composite statuses.
 */
export function computeLineStatusFromTree(roots: SpanNode[]): CovStatus {
  if (roots.length === 0) return CovStatus.CovComplete;

  let result: CovStatus = CovStatus.Uncovered;
  for (const root of roots) {
    result = maxStatus(result, root.compositeStatus);
  }
  return result;
}

/**
 * Compute per-line coverage status using span-tree algorithm.
 * Two-level: best-case within same span, worst-case across distinct spans.
 */
export function computeSpanTreeLineStatus(
  graph: ProofGraph,
  sourceCode: string,
): CovStatus[] {
  const lines = sourceCode.split("\n");
  const lineCount = lines.length;
  const result: CovStatus[] = new Array(lineCount).fill(CovStatus.CovComplete);

  // Group by line → span key → best status
  const lineSpans = new Map<number, Map<string, CovStatus>>();

  for (const node of graph.getAllNodes()) {
    const line = node.start.line;
    if (line < 1 || line > lineCount) continue;
    const spanKey = `${node.start.line},${node.start.col}-${node.end.line},${node.end.col}`;
    const idx = line - 1;

    if (!lineSpans.has(idx)) lineSpans.set(idx, new Map());
    const spans = lineSpans.get(idx)!;
    const existing = spans.get(spanKey);
    if (existing === undefined) {
      spans.set(spanKey, node.getCovStatus());
    } else {
      spans.set(spanKey, maxStatus(existing, node.getCovStatus()));
    }
  }

  // Worst-case across distinct spans
  for (const [idx, spans] of lineSpans) {
    let lineStatus: CovStatus = CovStatus.CovComplete;
    for (const spanStatus of spans.values()) {
      lineStatus = minStatus(lineStatus, spanStatus);
    }
    result[idx] = lineStatus;
  }

  return result;
}
