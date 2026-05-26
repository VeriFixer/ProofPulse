import { CovStatus } from "./types.js";
import { Node } from "./node.js";
import { ProofGraph } from "./proof-graph.js";

function escapeHtml(str: string): string {
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

interface Range {
  startIndex: number;
  endIndex: number;
  token: Node;
  children: Range[];
}

function tokenAttrs(tok: Node): { dataId: string; dataStatus: string; classes: string; istopAttr: string } {
  let statusStr = "";
  if (tok.getCovStatus() === CovStatus.Uncovered) statusStr = "uncovered";
  else if (tok.getCovStatus() === CovStatus.CovTest) statusStr = "covered-test";
  else statusStr = "covered-complete";

  const dataId = escapeHtml(tok.getId());
  const dataStatus = escapeHtml(statusStr);
  const classes = escapeHtml("token");
  const istopAttr = tok.isTopAssertion ? ' data-istop="true"' : "";
  return { dataId, dataStatus, classes, istopAttr };
}

/**
 * Generate an HTML fragment with nested <span> elements for each proof token.
 */
export function generateSpansFragment(code: string, graph: ProofGraph): string {
  const lines = code.split("\n");
  const lineStart: number[] = new Array(lines.length + 2);
  let pos = 0;
  for (let i = 0; i < lines.length; ++i) {
    lineStart[i + 1] = pos;
    pos += lines[i].length + 1;
  }

  const ranges: Range[] = [];
  const tokensArray = graph.getAllNodes();
  for (const t of tokensArray) {
    if (!t || !t.start || !t.end) continue;
    const sLine = t.start.line, sCol = t.start.col, eLine = t.end.line, eCol = t.end.col;
    if (!Number.isInteger(sLine) || !Number.isInteger(sCol) || !Number.isInteger(eLine) || !Number.isInteger(eCol)) continue;
    if (sLine < 1 || sLine > lines.length || eLine < 1 || eLine > lines.length) continue;
    const startIndex = lineStart[sLine] + Math.max(0, sCol - 1);
    const endIndex = lineStart[eLine] + eCol;
    if (isNaN(startIndex) || isNaN(endIndex) || startIndex < 0 || endIndex < startIndex) continue;
    ranges.push({ startIndex, endIndex, token: t, children: [] });
  }

  ranges.sort((a, b) => a.startIndex - b.startIndex || b.endIndex - a.endIndex);

  // Resolve partial overlaps
  for (let i = 0; i < ranges.length; i++) {
    for (let j = i + 1; j < ranges.length; j++) {
      const a = ranges[i], b = ranges[j];
      if (b.startIndex < a.endIndex && b.endIndex > a.endIndex) {
        const aSize = a.endIndex - a.startIndex;
        const bSize = b.endIndex - b.startIndex;
        if (bSize <= aSize) {
          a.endIndex = b.startIndex;
        } else {
          b.startIndex = a.endIndex;
        }
      }
    }
  }

  const validRanges = ranges.filter(r => r.startIndex < r.endIndex);
  validRanges.sort((a, b) => a.startIndex - b.startIndex || b.endIndex - a.endIndex);

  const roots: Range[] = [];
  const stack: Range[] = [];
  for (const r of validRanges) {
    while (stack.length && r.startIndex >= stack[stack.length - 1].endIndex) stack.pop();

    if (stack.length === 0) {
      roots.push(r);
      stack.push(r);
    } else {
      const parent = stack[stack.length - 1];
      if (r.endIndex <= parent.endIndex) {
        parent.children.push(r);
        stack.push(r);
      }
    }
  }

  function renderNode(node: Range, depth: number): string {
    const { dataId, dataStatus, classes, istopAttr } = tokenAttrs(node.token);
    const hasChildren = node.children.length > 0;
    const depthClass = `depth-${depth}`;
    const parentClass = hasChildren ? " has-children" : "";
    let innerOut = "";
    let cursor = node.startIndex;
    if (hasChildren) {
      node.children.sort((a, b) => a.startIndex - b.startIndex);
      for (const child of node.children) {
        if (cursor < child.startIndex) innerOut += escapeHtml(code.slice(cursor, child.startIndex));
        innerOut += renderNode(child, depth + 1);
        cursor = child.endIndex;
      }
    }
    if (cursor < node.endIndex) innerOut += escapeHtml(code.slice(cursor, node.endIndex));
    return `<span class="${classes} ${depthClass}${parentClass}" data-id="${dataId}" data-depth="${depth}" ${istopAttr} data-status="${dataStatus}">${innerOut}</span>`;
  }

  let out = "";
  let cursor = 0;
  roots.sort((a, b) => a.startIndex - b.startIndex);
  for (const rootNode of roots) {
    if (cursor < rootNode.startIndex) out += escapeHtml(code.slice(cursor, rootNode.startIndex));
    out += renderNode(rootNode, 0);
    cursor = rootNode.endIndex;
  }
  if (cursor < code.length) out += escapeHtml(code.slice(cursor));
  return out;
}

/** Return all nodes that prove a given top node (its provedBy set). */
export function getDependsOn(key: string, graph: ProofGraph): { node: Node; depth: number }[] | null {
  const node = graph.getNode(key);
  if (!node) return null;
  if ("provedBy" in node) {
    const provedBy = (node as any).provedBy as Set<Node>;
    return Array.from(provedBy).map(n => ({ node: n, depth: 1 }));
  }
  return [];
}

/** Return provedBy nodes for a top node. */
export function getProvedBy(key: string, graph: ProofGraph): { node: Node; depth: number }[] | null {
  const node = graph.getNode(key);
  if (!node) return null;
  if ("provedBy" in node) {
    const provedBy = (node as any).provedBy as Set<Node>;
    return Array.from(provedBy).map(n => ({ node: n, depth: 1 }));
  }
  return [];
}

/** Return top nodes that this node proves (tops where this node is in provedBy). */
export function getProves(key: string, graph: ProofGraph): { node: Node; depth: number }[] | null {
  const node = graph.getNode(key);
  if (!node) return null;
  const result: { node: Node; depth: number }[] = [];
  for (const top of graph.getAllTopNodes()) {
    if (top.provedBy.has(node)) {
      result.push({ node: top, depth: 1 });
    }
  }
  return result;
}
