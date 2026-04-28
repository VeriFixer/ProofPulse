import { CovStatus } from "./types.js";
import { ProofGraph, type BFSResult } from "./proof-graph.js";
import type { Node } from "./node.js";

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
  if (tok && tok.covStatus) {
    if (tok.covStatus === CovStatus.Uncovered) statusStr = "uncovered";
    else if (tok.covStatus === CovStatus.CovTest) statusStr = "covered-test";
    else statusStr = "covered-complete";
  }
  const dataId = escapeHtml(tok.id);
  const dataStatus = escapeHtml(statusStr);
  const classes = escapeHtml("token");
  const istopAttr = tok.isTopAssertion ? ' data-istop="true"' : "";
  return { dataId, dataStatus, classes, istopAttr };
}

/**
 * Generate an HTML fragment with nested <span> elements for each proof token.
 * Pure function — no DOM dependency.
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

  const roots: Range[] = [];
  const stack: Range[] = [];
  for (const r of ranges) {
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
      // partial overlap: skip
    }
  }

  function renderNode(node: Range): string {
    const { dataId, dataStatus, classes, istopAttr } = tokenAttrs(node.token);
    let innerOut = "";
    let cursor = node.startIndex;
    if (node.children.length) {
      node.children.sort((a, b) => a.startIndex - b.startIndex);
      for (const child of node.children) {
        if (cursor < child.startIndex) innerOut += escapeHtml(code.slice(cursor, child.startIndex));
        innerOut += renderNode(child);
        cursor = child.endIndex;
      }
    }
    if (cursor < node.endIndex) innerOut += escapeHtml(code.slice(cursor, node.endIndex));
    return `<span class="${classes}" data-id="${dataId}" ${istopAttr} data-status="${dataStatus}">${innerOut}</span>`;
  }

  let out = "";
  let cursor = 0;
  roots.sort((a, b) => a.startIndex - b.startIndex);
  for (const rootNode of roots) {
    if (cursor < rootNode.startIndex) out += escapeHtml(code.slice(cursor, rootNode.startIndex));
    out += renderNode(rootNode);
    cursor = rootNode.endIndex;
  }
  if (cursor < code.length) out += escapeHtml(code.slice(cursor));
  return out;
}

/** Return all BFS neighbors (both directions) for a node by key. */
export function getDependsOn(key: string, graph: ProofGraph, maxDepth?: number): BFSResult[] | null {
  if (!graph.hasNode(key)) return null;
  return graph.getBFSNeighbors(key, false, true, maxDepth);
}
