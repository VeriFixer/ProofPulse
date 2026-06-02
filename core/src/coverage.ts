import { CovStatus, TokenType } from "./types.js";
import { ProofNode } from "./proof-node.js";
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
 * Pass 2: Set covStatus (semantic/final) on all nodes based on covStatusInternal
 * and call connection relationships.
 *
 * Preconditions:
 *   - CovComplete: used to prove a postcondition (internal = CovComplete)
 *   - CovTest: only used in a call situation (is a connection target)
 *   - Uncovered: totally unused
 *
 * Postconditions:
 *   - CovTest: proved (has provedBy children) but not used in a call
 *   - CovComplete: used in a call (another method relies on this postcondition)
 *   - Uncovered: not proved
 */
export function applyCoverageSemantic(graph: ProofGraph): void {
  const allNodes = graph.getAllNodes();

  // Build connection target spans for span-based matching
  // (a node is "used in a call" if its span matches any connection target)
  const connectionTargetSpans = new Set<string>();
  for (const node of allNodes) {
    for (const target of node.connections) {
      const span = `${target.file}|${target.start.line},${target.start.col}-${target.end.line},${target.end.col}`;
      connectionTargetSpans.add(span);
    }
  }

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

  // Preconditions:
  //   CovComplete → used to prove a postcondition (internal = CovComplete)
  //   CovTest → used in a call (span matches a connection target)
  //   Uncovered → totally unused
  for (const node of allNodes) {
    if (node.getType() === TokenType.Precondition) {
      if (node.getCovStatusInternal() === CovStatus.CovComplete) {
        node.setCovStatus(CovStatus.CovComplete);
      } else {
        const span = `${node.file}|${node.start.line},${node.start.col}-${node.end.line},${node.end.col}`;
        if (connectionTargetSpans.has(span)) {
          node.setCovStatus(CovStatus.CovTest);
        } else {
          node.setCovStatus(CovStatus.Uncovered);
        }
      }
    }
  }

  // Postconditions:
  //   CovComplete → proved by real code AND is a connection target (used in a call)
  //   CovTest → proved by real code but not used in a call
  //   Uncovered → not proved by real code (only itself or nothing)
  for (const node of allNodes) {
    if (node.getType() === TokenType.Postcondition) {
      // Check if proved by real code: provedBy has nodes other than itself
      let hasRealProver = false;
      if (node.roles.isTop) {
        for (const dep of node.provedBy) {
          if (dep !== node) {
            hasRealProver = true;
            break;
          }
        }
      }

      // Check if this postcondition is a connection target (by span match)
      const span = `${node.file}|${node.start.line},${node.start.col}-${node.end.line},${node.end.col}`;
      const isUsedInCall = connectionTargetSpans.has(span);

      if (hasRealProver && isUsedInCall) {
        node.setCovStatus(CovStatus.CovComplete);
      } else if (hasRealProver) {
        node.setCovStatus(CovStatus.CovTest);
      } else if (!node.roles.isTop && node.getCovStatusInternal() === CovStatus.CovComplete) {
        // Non-top postcondition that contributes to proving another postcondition
        node.setCovStatus(CovStatus.CovComplete);
      } else {
        node.setCovStatus(CovStatus.Uncovered);
      }
    }
  }
}

/**
 * Run both coverage passes on a graph.
 * Also propagates coverage through call connections.
 */
export function applyCoverage(graph: ProofGraph): void {
  applyCoverageInternal(graph);
  applyCoverageConnections(graph);
  applyCoverageSemantic(graph);
}

/**
 * Propagate coverage through call connections.
 * If a call node has coverage (CovComplete/CovTest internally),
 * its connection targets inherit that coverage.
 */
function applyCoverageConnections(graph: ProofGraph): void {
  const callNodes = graph.getAllCallNodes();
  for (const call of callNodes) {
    const callStatus = call.getCovStatusInternal();
    if (callStatus === CovStatus.Uncovered) continue;

    for (const target of call.connections) {
      if (target.getCovStatusInternal() === CovStatus.Uncovered) {
        target.setCovStatusInternal(callStatus);
      }
    }
  }
}

/**
 * Compute per-line coverage status.
 * 
 * Strategy:
 * 1. Group nodes by exact span (startLine,startCol-endLine,endCol)
 * 2. Within each span group: best-case (CovComplete > CovTest > Uncovered)
 *    — same code used in multiple contexts, if any covers it, it's covered
 * 3. Across distinct spans on same line: worst-case (Uncovered > CovTest > CovComplete)
 *    — different code on same line, if any part is uncovered the line is flagged
 * 
 * Default is CovComplete for lines with no tokens.
 */
export function computeLineStatus(graph: ProofGraph, sourceCode: string): CovStatus[] {
  const lines = sourceCode.split("\n");
  const result: CovStatus[] = new Array(lines.length).fill(CovStatus.CovComplete);
  const nodes = graph.getAllNodes();

  // Group by line, then by span key within each line
  const lineSpans = new Map<number, Map<string, CovStatus>>();

  for (const node of nodes) {
    if (!node || !node.start || !node.end) continue;
    const idx = Math.max(0, node.start.line - 1);
    if (idx >= result.length) continue;

    const spanKey = `${node.start.line},${node.start.col}-${node.end.line},${node.end.col}`;
    const nodeStatus = node.getCovStatus();

    if (!lineSpans.has(idx)) lineSpans.set(idx, new Map());
    const spans = lineSpans.get(idx)!;

    const existing = spans.get(spanKey);
    if (existing === undefined) {
      spans.set(spanKey, nodeStatus);
    } else {
      // Best-case within same span
      spans.set(spanKey, bestStatus(existing, nodeStatus));
    }
  }

  // Worst-case across distinct spans on same line
  for (const [idx, spans] of lineSpans) {
    let lineStatus: CovStatus = CovStatus.CovComplete;
    for (const spanStatus of spans.values()) {
      lineStatus = worstStatus(lineStatus, spanStatus);
    }
    result[idx] = lineStatus;
  }

  return result;
}

function bestStatus(a: CovStatus, b: CovStatus): CovStatus {
  const rank: Record<CovStatus, number> = {
    [CovStatus.CovComplete]: 2,
    [CovStatus.CovTest]: 1,
    [CovStatus.Uncovered]: 0,
  };
  return rank[a] >= rank[b] ? a : b;
}

function worstStatus(a: CovStatus, b: CovStatus): CovStatus {
  const rank: Record<CovStatus, number> = {
    [CovStatus.CovComplete]: 2,
    [CovStatus.CovTest]: 1,
    [CovStatus.Uncovered]: 0,
  };
  return rank[a] <= rank[b] ? a : b;
}

/** Return all nodes whose source span includes the given line (1-based). */
export function getNodesByLine(graph: ProofGraph, line: number): ProofNode[] {
  return graph.getAllNodes().filter(
    (n) => n.start.line <= line && line <= n.end.line,
  );
}
