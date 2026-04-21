import { type NodeData, TokenType, CovStatus } from "@proofpulse/core";

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

/** Check if a node is a loop invariant by its prooftext. */
function isInvariantNode(n: NodeData): boolean {
  return n.prooftext.includes("loop invariant");
}

/**
 * Postcondition classification (matches paper's "Postconditions" column):
 * Strong iff ≥1 postcondition with CovTest/CovComplete AND all body nodes CovComplete.
 * Ignores precondition coverage state.
 */
export function classifyPostcondition(nodes: NodeData[]): "strong" | "weak" | "none" {
  const postconditions = nodes.filter((n) => n.type === TokenType.Postcondition);
  if (postconditions.length === 0) return "none";

  const bodyNodes = nodes.filter(
    (n) => n.type === TokenType.CodeLine && !isInvariantNode(n)
  );

  const allPostCovered = postconditions.every(
    (n) => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest
  );
  if (!allPostCovered) return "weak";

  const allBodyComplete = bodyNodes.every(
    (n) => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest
  );
  if (!allBodyComplete) return "weak";

  return "strong";
}

/**
 * Precondition classification (matches paper's "Preconditions" column):
 * Required = ALL preconditions are covered (CovComplete/CovTest) → all are used by the proof.
 * Optional = ANY precondition is Uncovered → worst result wins.
 */
export function classifyPrecondition(nodes: NodeData[]): "required" | "optional" | "none" {
  const preconditions = nodes.filter((n) => n.type === TokenType.Precondition);
  if (preconditions.length === 0) return "none";

  const anyUncovered = preconditions.some(
    (n) => n.covStatus === CovStatus.Uncovered
  );
  return anyUncovered ? "optional" : "required";
}

/**
 * Invariant classification (matches paper's "Invariants" column):
 * Strong iff all invariant nodes have CovComplete/CovTest.
 * Weak if any invariant is Uncovered.
 */
export function classifyInvariant(nodes: NodeData[]): "strong" | "weak" | "none" {
  const invariants = nodes.filter((n) => isInvariantNode(n));
  if (invariants.length === 0) return "none";

  const allCovered = invariants.every(
    (n) => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest
  );
  return allCovered ? "strong" : "weak";
}

/** Overall classification: strong postcondition = strong, else weak. */
export function classifySpec(nodes: NodeData[]): "strong" | "weak" {
  const post = classifyPostcondition(nodes);
  return post === "strong" ? "strong" : "weak";
}

/** Classify all three categories at once. */
export function classifyAll(nodes: NodeData[]): CategoryClassification {
  return {
    postcondition: classifyPostcondition(nodes),
    precondition: classifyPrecondition(nodes),
    invariant: classifyInvariant(nodes),
  };
}
