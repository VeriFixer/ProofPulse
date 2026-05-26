import { CovStatus, TokenType } from "./types.js";
import { Node, TopNode } from "./node.js";
import { ProofGraph } from "./proof-graph.js";

/**
 * Pass 1: Set covStatusInternal on all nodes.
 * - Postcondition tops + their provedBy → CovComplete
 * - Other tops with provedBy children: propagate CovTest (or CovComplete if child already CovComplete)
 * - AssertionAutomatic tops: children get CovComplete
 */
export function applyCoverageInternal(graph: ProofGraph): void {
  const tops = graph.getAllTopNodes();

  // Postcondition tops: mark self + provedBy as CovComplete internally
  const postTops = tops.filter(t => t.getType() === TokenType.Postcondition);
  for (const post of postTops) {
    post.setCovStatusInternal(CovStatus.CovComplete);
    for (const dep of post.provedBy) {
      dep.setCovStatusInternal(CovStatus.CovComplete);
    }
  }

  // Non-postcondition tops
  const otherTops = tops.filter(t => t.getType() !== TokenType.Postcondition);
  for (const top of otherTops) {
    if (top.provedBy.size === 0) continue;

    // If not manual assertion or loop invariant, mark top as CovComplete internally
    if (top.getType() !== TokenType.AssertionManual && top.getType() !== TokenType.LoopInvariant) {
      top.setCovStatusInternal(CovStatus.CovComplete);
    }

    for (const dep of top.provedBy) {
      if (dep.getCovStatusInternal() === CovStatus.CovComplete) {
        top.setCovStatusInternal(CovStatus.CovComplete);
      }

      if (top.getType() === TokenType.AssertionAutomatic) {
        dep.setCovStatusInternal(CovStatus.CovComplete);
        dep.setCovStatus(CovStatus.CovComplete);
      } else if (dep.getCovStatusInternal() !== CovStatus.CovComplete) {
        dep.setCovStatusInternal(CovStatus.CovTest);
      }
    }
  }
}

/**
 * Pass 2: Set covStatus (semantic/final) on all nodes based on covStatusInternal.
 */
export function applyCoverageSemantic(graph: ProofGraph): void {
  const allNodes = graph.getAllNodes();
  const tops = graph.getAllTopNodes();

  // CodeLines: covStatus = covStatusInternal
  for (const node of allNodes) {
    if (node.getType() === TokenType.CodeLine) {
      node.setCovStatus(node.getCovStatusInternal());
    }
  }

  // ManualAssertions: CovComplete if internal is CovComplete, else Uncovered
  for (const node of allNodes) {
    if (node.getType() === TokenType.AssertionManual) {
      node.setCovStatus(
        node.getCovStatusInternal() === CovStatus.CovComplete
          ? CovStatus.CovComplete
          : CovStatus.Uncovered
      );
    }
  }

  // LoopInvariants: CovComplete if internal is CovComplete, else Uncovered
  for (const node of allNodes) {
    if (node.getType() === TokenType.LoopInvariant) {
      node.setCovStatus(
        node.getCovStatusInternal() === CovStatus.CovComplete
          ? CovStatus.CovComplete
          : CovStatus.Uncovered
      );
    }
  }

  // AssertionAutomatic: always CovComplete
  for (const node of allNodes) {
    if (node.getType() === TokenType.AssertionAutomatic) {
      node.setCovStatus(CovStatus.CovComplete);
    }
  }

  // Call: covStatus = covStatusInternal
  for (const node of allNodes) {
    if (node.getType() === TokenType.Call) {
      node.setCovStatus(node.getCovStatusInternal());
    }
  }

  // Preconditions: covStatus = covStatusInternal
  for (const node of allNodes) {
    if (node.getType() === TokenType.Precondition) {
      node.setCovStatus(node.getCovStatusInternal());
    }
  }

  // Postconditions (top): check if any provedBy child is CovComplete
  const postTops = tops.filter(t => t.getType() === TokenType.Postcondition);
  for (const post of postTops) {
    let anyChildCovComplete = false;
    for (const dep of post.provedBy) {
      if (dep.getType() !== TokenType.Postcondition && dep.getCovStatus() === CovStatus.CovComplete) {
        anyChildCovComplete = true;
        break;
      }
    }

    if (anyChildCovComplete) {
      // If this postcondition is itself used by another top (has proofUnused references from other tops),
      // mark CovComplete; otherwise CovTest
      post.setCovStatus(CovStatus.CovTest);
    }
  }

  // Non-top postconditions: covStatus = covStatusInternal
  for (const node of allNodes) {
    if (node.getType() === TokenType.Postcondition && !node.isTopAssertion) {
      node.setCovStatus(node.getCovStatusInternal());
    }
  }
}

/**
 * Run both coverage passes on a graph.
 */
export function applyCoverage(graph: ProofGraph): void {
  applyCoverageInternal(graph);
  applyCoverageSemantic(graph);
}

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

    if (node.getCovStatus() === CovStatus.Uncovered) {
      result[idx] = CovStatus.Uncovered;
    } else if (node.getCovStatus() === CovStatus.CovTest) {
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
