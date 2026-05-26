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
 * Compute line status from tree roots.
 * Line status = min over root span composite statuses.
 */
export function computeLineStatusFromTree(roots: SpanNode[]): CovStatus {
  if (roots.length === 0) return CovStatus.CovComplete;

  let result: CovStatus = CovStatus.CovComplete;
  for (const root of roots) {
    result = minStatus(result, root.compositeStatus);
  }
  return result;
}

/**
 * Compute per-line coverage status using span-tree algorithm.
 */
export function computeSpanTreeLineStatus(
  graph: ProofGraph,
  sourceCode: string,
): CovStatus[] {
  const lines = sourceCode.split("\n");
  const lineCount = lines.length;
  const result: CovStatus[] = new Array(lineCount).fill(CovStatus.CovComplete);

  const nodesByLine = new Map<number, Array<{ nodeId: string; startCol: number; endCol: number; compositeStatus: CovStatus }>>();

  for (const node of graph.getAllNodes()) {
    const line = node.start.line;
    if (line < 1 || line > lineCount) continue;
    if (!nodesByLine.has(line)) nodesByLine.set(line, []);
    const existing = nodesByLine.get(line)!;
    if (!existing.some((e) => e.nodeId === node.getId())) {
      existing.push({
        nodeId: node.getId(),
        startCol: node.start.col,
        endCol: node.end.col,
        compositeStatus: node.getCovStatus(),
      });
    }
  }

  for (const [line, nodes] of nodesByLine) {
    const roots = buildSpanTree(nodes);
    const status = computeLineStatusFromTree(roots);
    result[line - 1] = status;
  }

  return result;
}
