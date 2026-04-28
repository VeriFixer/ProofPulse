import * as vscode from "vscode";
import { ProofGraph, getNodesByLine, getRelatedNodes } from "@proofpulse/core";

export class ProofPulseHoverProvider implements vscode.HoverProvider {
  constructor(private graph: ProofGraph) {}

  provideHover(
    document: vscode.TextDocument,
    position: vscode.Position
  ): vscode.Hover | undefined {
    const line = position.line + 1; // 1-based
    const col = position.character + 1; // 1-based
    const nodes = getNodesByLine(this.graph, line);

    // Find node whose column span contains cursor
    const node = nodes.find(
      (n) =>
        (n.start.line < line || (n.start.line === line && n.start.col <= col)) &&
        (n.end.line > line || (n.end.line === line && n.end.col >= col))
    );

    if (!node) {
      return undefined;
    }

    const related = getRelatedNodes(this.graph, node.id) ?? [];

    const md = new vscode.MarkdownString();
    md.appendMarkdown(`**Status:** ${node.covStatus}\n\n`);
    md.appendMarkdown(`**Message:** ${node.prooftext}\n\n`);
    md.appendMarkdown(`**Loc:** ${node.id}\n\n`);
    md.appendMarkdown(`**Kind:** ${node.type}\n\n`);
    md.appendMarkdown(`**CovInternal:** ${node.covStatusInternal}\n\n`);

    if (related.length > 0) {
      md.appendMarkdown(`**All Related (${related.length}):**\n\n`);
      for (const r of related) {
        md.appendMarkdown(`- ${r.id} — ${r.prooftext}\n`);
      }
    }

    return new vscode.Hover(md);
  }
}
