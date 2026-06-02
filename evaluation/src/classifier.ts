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
 * Postcondition classification:
 * Only consider tops with method-type correctness (skip well-formedness → always strong).
 * For each correctness postcondition top, collect provedBy ∪ proofUnused nodes.
 * If any node in that set is Uncovered → weak.
 * If all covered (CovComplete or CovTest) → strong.
 */
export function classifyPostcondition(graph: ProofGraph): "strong" | "weak" | "none" {
  const topNodes = graph.getAllTopNodes();
  const postTops = topNodes.filter(n => n.getType() === TokenType.Postcondition);
  if (postTops.length === 0) return "none";

  // Only consider correctness (method) type tops
  const methodTops = postTops.filter(n => !n.methodType.includes("well-formedness"));
  // If all postcondition tops are well-formedness, classify as strong
  if (methodTops.length === 0) return "strong";

  // For each method-type top, check if all CodeLine nodes in provedBy ∪ proofUnused are covered
  for (const top of methodTops) {
    const deps = new Set([...top.provedBy, ...top.proofUnused]);
    const codeLineDeps = [...deps].filter(d => d.getType() === TokenType.CodeLine);
    // Empty code line deps means nothing substantive proves this postcondition → weak
    if (codeLineDeps.length === 0) return "weak";
    for (const dep of codeLineDeps) {
      if (dep.covStatus === CovStatus.Uncovered) return "weak";
    }
  }

  return "strong";
}

/**
 * Precondition classification — only consider correctness methodType (skip well-formedness).
 */
export function classifyPrecondition(nodes: NodeData[]): "required" | "optional" | "none" {
  const preconditions = nodes.filter(
    (n) => n.type === TokenType.Precondition && !(n.methodType ?? "").includes("well-formedness")
  );
  if (preconditions.length === 0) return "none";

  const allCovered = preconditions.every(
    (n) => (n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest)
  );
  return allCovered ? "required" : "optional";
}

/**
 * Invariant classification:
 * Only consider tops with method-type correctness (skip well-formedness → always strong).
 * For each correctness invariant top, collect provedBy ∪ proofUnused nodes.
 * If any node in that set is Uncovered → weak.
 * If all covered (CovComplete or CovTest) → strong.
 */
export function classifyInvariant(graph: ProofGraph): "strong" | "weak" | "none" {
  const topNodes = graph.getAllTopNodes();
  const invTops = topNodes.filter(n => n.getType() === TokenType.LoopInvariant);
  if (invTops.length === 0) return "none";

  // Only consider correctness (method) type tops
  const methodTops = invTops.filter(n => !n.methodType.includes("well-formedness"));
  // If all invariant tops are well-formedness, classify as strong
  if (methodTops.length === 0) return "strong";

  // For each method-type top, check if all CodeLine nodes in provedBy ∪ proofUnused are covered
  for (const top of methodTops) {
    const deps = new Set([...top.provedBy, ...top.proofUnused]);
    const codeLineDeps = [...deps].filter(d => d.getType() === TokenType.CodeLine);
    // Empty code line deps means nothing substantive proves this invariant → weak
    if (codeLineDeps.length === 0) return "weak";
    for (const dep of codeLineDeps) {
      if (dep.covStatus === CovStatus.Uncovered) return "weak";
    }
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
