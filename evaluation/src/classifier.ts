import { type ProofGraph, type NodeData, TokenType, CovStatus, UnitKind } from "@proofpulse/core";
import { Classification, OracleLabel, PreconditionNeed, SpecStrength } from "./types.js";

/** The node fields precondition classification needs (satisfied by ProofNode and NodeData). */
export type PreconditionNodeInfo = Pick<NodeData, "type" | "covStatus" | "methodType" | "methodName">;

export interface CategoryClassification {
  postcondition: SpecStrength;
  precondition: PreconditionNeed;
  invariant: SpecStrength;
}

/** Classification of one method (Dafny's unit name, e.g. `M.C.Foo`). */
export interface MethodClassification {
  method: string;
  classification: Classification.Strong | Classification.Weak;
  categories: CategoryClassification;
}

export interface ClassificationResult {
  taskId: string;
  filePath: string;
  classification: Classification;
  categories: CategoryClassification;
  oracleLabel: OracleLabel;
  postconditionLines: number[];
  preconditionLines: number[];
  invariantLines: number[];
  bodyLines: number[];
  coverageStatuses: Record<number, CovStatus>;
  error?: string;
}

/** Nodes whose coverage decides strength: code lines and the atoms of if/while conditions. */
const DECIDING = new Set<TokenType>([TokenType.CodeLine, TokenType.Condition]);

/**
 * Strength of the correctness tops of one type (postconditions or invariants),
 * optionally only those of one method. Well-formedness tops are skipped (all
 * well-formedness → strong). For each top, collect provedBy ∪ proofUnused;
 * only code lines and condition atoms count. If there are none, or any of
 * them is Uncovered or CovTest → weak: some code, or some way a condition
 * evaluates, is not pinned down by the spec. If all are CovComplete → strong.
 */
function classifyTops(graph: ProofGraph, type: TokenType, method?: string): SpecStrength {
  const tops = graph.getAllTopNodes().filter(n => n.getType() === type && (method === undefined || n.methodName === method));
  if (tops.length === 0) return SpecStrength.None;

  const methodTops = tops.filter(n => n.methodType !== UnitKind.WellFormedness);
  if (methodTops.length === 0) return SpecStrength.Strong;

  for (const top of methodTops) {
    const deps = [...new Set([...top.provedBy, ...top.proofUnused])].filter(d => DECIDING.has(d.getType()));
    // Nothing substantive proves this top → weak
    if (deps.length === 0) return SpecStrength.Weak;
    for (const dep of deps) {
      if (dep.covStatus === CovStatus.Uncovered || dep.covStatus === CovStatus.CovTest) return SpecStrength.Weak;
    }
  }

  return SpecStrength.Strong;
}

/** Postcondition strength of the whole file, or of one method. */
export function classifyPostcondition(graph: ProofGraph, method?: string): SpecStrength {
  return classifyTops(graph, TokenType.Postcondition, method);
}

/**
 * Precondition classification — only consider correctness methodType (skip well-formedness).
 * Optional only when every such precondition is Uncovered; otherwise required.
 */
export function classifyPrecondition(nodes: readonly PreconditionNodeInfo[], method?: string): PreconditionNeed {
  const preconditions = nodes.filter(
    (n) => n.type === TokenType.Precondition && n.methodType !== UnitKind.WellFormedness
      && (method === undefined || n.methodName === method)
  );
  if (preconditions.length === 0) return PreconditionNeed.None;

  const allUncovered = preconditions.every(
    (n) => (n.covStatus === CovStatus.Uncovered)
  );
  return allUncovered ? PreconditionNeed.Optional : PreconditionNeed.Required;
}

/** Invariant strength of the whole file, or of one method. */
export function classifyInvariant(graph: ProofGraph, method?: string): SpecStrength {
  return classifyTops(graph, TokenType.LoopInvariant, method);
}

/** Overall classification (of the file, or of one method): strong postcondition = strong, else weak. */
export function classifySpec(graph: ProofGraph, method?: string): Classification.Strong | Classification.Weak {
  const post = classifyPostcondition(graph, method);
  return post === SpecStrength.Strong ? Classification.Strong : Classification.Weak;
}

/** Classify all three categories at once. */
export function classifyAll(graph: ProofGraph, nodes: readonly PreconditionNodeInfo[], method?: string): CategoryClassification {
  return {
    postcondition: classifyPostcondition(graph, method),
    precondition: classifyPrecondition(nodes, method),
    invariant: classifyInvariant(graph, method),
  };
}

/**
 * Classify each method that has a correctness proof on its own, so that a weak
 * method does not make the other methods of its file weak.
 */
export function classifyMethods(graph: ProofGraph, nodes: readonly PreconditionNodeInfo[]): MethodClassification[] {
  const methods = new Set<string>();
  for (const n of graph.getAllNodes()) {
    if (n.methodType === UnitKind.Correctness) methods.add(n.methodName);
  }
  return [...methods].sort().map(method => ({
    method,
    classification: classifySpec(graph, method),
    categories: classifyAll(graph, nodes, method),
  }));
}
