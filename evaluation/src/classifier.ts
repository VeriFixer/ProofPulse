import { type ProofGraph, type NodeData, TokenType, CovStatus } from "@proofpulse/core";

export interface CategoryClassification {
  postcondition: "strong" | "weak" | "none";
  precondition: "required" | "optional" | "none";
  invariant: "strong" | "weak" | "none";
}

export interface ClassificationResult {
  taskId: string;
  filePath: string;
  classification: "strong" | "weak" | "error";
  categories: CategoryClassification;
  oracleLabel: "strong" | "weak" | "wrong";
  postconditionLines: number[];
  preconditionLines: number[];
  invariantLines: number[];
  bodyLines: number[];
  coverageStatuses: Record<number, CovStatus>;
  error?: string;
}

/**
 * Scoped postcondition classification:
 * Strong iff all postcondition tops are covered AND all nodes in their combined scope are covered.
 * No fallback — if scope is empty, tops being covered is sufficient.
 */
export function classifyPostcondition(graph: ProofGraph): "strong" | "weak" | "none" {
  const topNodes = graph.getAllTopNodes();
  const postTops = topNodes.filter(n => n.type === TokenType.Postcondition);
  if (postTops.length === 0) return "none";

  // All postcondition tops must be covered
  const allPostCovered = postTops.every(
    n => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest
  );
  if (!allPostCovered) return "weak";

  // Union of all postcondition scopes (BFS deps + scope set)
  const scopeIds = new Set<string>();
  for (const top of postTops) {
    const fullScope = graph.getFullScope(top.id);
    for (const id of fullScope) scopeIds.add(id);
  }

  // If scope is empty, tops being covered is sufficient
  if (scopeIds.size === 0) return "strong";

  // Check all scope nodes are covered
  for (const id of scopeIds) {
    const node = graph.getNode(id);
    if (node && node.covStatus === CovStatus.Uncovered) return "weak";
  }

  return "strong";
}

/**
 * Precondition classification unchanged — still takes NodeData[].
 */
export function classifyPrecondition(nodes: NodeData[]): "required" | "optional" | "none" {
  const preconditions = nodes.filter((n) => n.type === TokenType.Precondition);
  if (preconditions.length === 0) return "none";

  const allCovered = preconditions.every(
    (n) => (n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest)
  );
  return allCovered ? "required" : "optional";
}

/**
 * Scoped invariant classification:
 * Strong iff all invariant tops are covered AND all nodes in their combined scope are covered.
 * No fallback — if scope is empty, tops being covered is sufficient.
 */
export function classifyInvariant(graph: ProofGraph): "strong" | "weak" | "none" {
  const topNodes = graph.getAllTopNodes();
  const invTops = topNodes.filter(n => n.type === TokenType.LoopInvariant);
  if (invTops.length === 0) return "none";

  // All invariant tops must be covered
  const allInvCovered = invTops.every(
    n => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest
  );
  if (!allInvCovered) return "weak";

  // Union of all invariant scopes (BFS deps + scope set)
  const scopeIds = new Set<string>();
  for (const top of invTops) {
    const fullScope = graph.getFullScope(top.id);
    for (const id of fullScope) scopeIds.add(id);
  }

  // If scope is empty, tops being covered is sufficient
  if (scopeIds.size === 0) return "strong";

  // Check all scope nodes are covered
  for (const id of scopeIds) {
    const node = graph.getNode(id);
    if (node && node.covStatus === CovStatus.Uncovered) return "weak";
  }

  return "strong";
}

/** Overall classification: strong postcondition = strong, else weak. */
export function classifySpec(graph: ProofGraph): "strong" | "weak" {
  const post = classifyPostcondition(graph);
  return post === "strong" ? "strong" : "weak";
}

/** Classify all three categories at once. */
export function classifyAll(graph: ProofGraph, nodes: NodeData[]): CategoryClassification {
  return {
    postcondition: classifyPostcondition(graph),
    precondition: classifyPrecondition(nodes),
    invariant: classifyInvariant(graph),
  };
}
