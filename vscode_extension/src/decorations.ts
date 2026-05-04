import * as path from "node:path";
import * as vscode from "vscode";
import { CovStatus, Node } from "@proofpulse/core";

interface DecorationTypes {
  uncoveredGutter: vscode.TextEditorDecorationType;
  covTestGutter: vscode.TextEditorDecorationType;
  uncoveredInline: vscode.TextEditorDecorationType;
  covTestInline: vscode.TextEditorDecorationType;
}

/** Module-level reference to current decoration types so clearDecorations can dispose them. */
let currentTypes: DecorationTypes | null = null;

/** Type-aware explanation for Uncovered status */
function uncoveredExplanation(type: string): string {
  switch (type) {
    case "Postcondition": return "Postcondition not proven by any code path.";
    case "Precondition": return "Precondition not used in any proof obligation.";
    case "AssertionManual": return "Manual assertion not covered by proof dependencies.";
    case "CodeLine": return "Code line not contributing to any proof obligation.";
    default: return "Not covered by any proof path.";
  }
}

/** Type-aware explanation for CovTest status */
function covTestExplanation(type: string): string {
  switch (type) {
    case "Postcondition": return "Postcondition not used in calling code (potentially unused method).";
    case "Precondition": return "Precondition only used in calling tests, unnecessary to prove postconditions.";
    case "CodeLine": return "Code used only by test assertions, not by postcondition proofs.";
    case "AssertionManual": return "Assertion covered only by test paths, not postcondition proofs.";
    default: return "Covered only by test/non-postcondition assertions.";
  }
}

export function createDecorationTypes(opacity: number, extensionPath: string): DecorationTypes {
  return {
    uncoveredGutter: vscode.window.createTextEditorDecorationType({
      isWholeLine: true,
      backgroundColor: `rgba(255, 0, 0, ${opacity})`,
      overviewRulerColor: "rgba(255, 0, 0, 0.6)",
      overviewRulerLane: vscode.OverviewRulerLane.Left,
      gutterIconPath: path.join(extensionPath, "media", "gutter-uncovered.svg"),
      gutterIconSize: "contain",
    }),
    covTestGutter: vscode.window.createTextEditorDecorationType({
      isWholeLine: true,
      backgroundColor: `rgba(255, 200, 0, ${opacity})`,
      overviewRulerColor: "rgba(255, 200, 0, 0.6)",
      overviewRulerLane: vscode.OverviewRulerLane.Left,
      gutterIconPath: path.join(extensionPath, "media", "gutter-covtest.svg"),
      gutterIconSize: "contain",
    }),
    uncoveredInline: vscode.window.createTextEditorDecorationType({
      // No particular text decoration apllied for now but can change
    }),
    covTestInline: vscode.window.createTextEditorDecorationType({
      // No particular text decoration apllied for now but can change
    }),
  };
}

export function applyDecorations(
  editor: vscode.TextEditor,
  lineStatus: CovStatus[],
  nodes: Node[],
  opacity: number,
  extensionPath: string,
): void {
  // Dispose old decoration types before creating fresh ones
  disposeCurrentTypes();
  const types = createDecorationTypes(opacity, extensionPath);
  currentTypes = types;

  const doc = editor.document;

  /** Extract a readable code snippet for a node. Falls back to full line if range is too small. */
  function nodeSnippet(n: Node): string {
    const startLine = Math.max(0, n.start.line - 1);
    const endLine = Math.max(0, n.end.line - 1);
    const startCol = Math.max(0, n.start.col - 1);
    const endCol = n.end.col;
    const range = new vscode.Range(startLine, startCol, endLine, endCol);
    let text = doc.getText(range).trim();
    // If extracted text is too short (single char like "=" or ">"), use the full line
    if (text.length <= 2 && startLine < doc.lineCount) {
      text = doc.lineAt(startLine).text.trim();
    }
    return text.length > 60 ? text.slice(0, 57) + "..." : text;
  }

  // Build maps: line index (0-based) → nodes on that line, by status
  const uncoveredNodesByLine = new Map<number, Node[]>();
  const covTestNodesByLine = new Map<number, Node[]>();
  for (const node of nodes) {
    const map = node.covStatus === CovStatus.Uncovered ? uncoveredNodesByLine
      : node.covStatus === CovStatus.CovTest ? covTestNodesByLine
        : null;
    if (!map) continue;
    for (let line = node.start.line; line <= node.end.line; line++) {
      const idx = line - 1;
      let arr = map.get(idx);
      if (!arr) { arr = []; map.set(idx, arr); }
      arr.push(node);
    }
  }

  // Gutter decorations with hover messages
  const uncoveredGutterOpts: vscode.DecorationOptions[] = [];
  const covTestGutterOpts: vscode.DecorationOptions[] = [];

  for (let i = 0; i < lineStatus.length; i++) {
    const status = lineStatus[i];
    if (status === CovStatus.Uncovered) {
      const lineNodes = uncoveredNodesByLine.get(i) ?? [];
      const hover = new vscode.MarkdownString(undefined, true);
      hover.isTrusted = true;
      hover.supportHtml = true;

      for (const n of lineNodes) {
        const shortSnippet = nodeSnippet(n);

        hover.appendMarkdown(`🔴 \`${shortSnippet}\` *(Line ${n.start.line}:${n.start.col})*  \n`);
        hover.appendMarkdown(`${uncoveredExplanation(n.type)}  \n\n`);
      }

      hover.appendMarkdown(`---\n`);
      hover.appendMarkdown(`[$(graph) Click to Generate Proof Coverage Report](command:proofpulse.getProofReport)`);

      uncoveredGutterOpts.push({
        range: new vscode.Range(i, 0, i, 0),
        hoverMessage: hover,
      });
    } else if (status === CovStatus.CovTest) {
      const lineNodes = covTestNodesByLine.get(i) ?? [];
      const hover = new vscode.MarkdownString(undefined, true);
      hover.isTrusted = true;
      hover.supportHtml = true;

      if (lineNodes.length > 0) {
        for (const n of lineNodes) {
          const shortSnippet = nodeSnippet(n);
          hover.appendMarkdown(`🟡 \`${shortSnippet}\` *(Line ${n.start.line}:${n.start.col})*  \n`);
          hover.appendMarkdown(`${covTestExplanation(n.type)}  \n\n`);
        }
      } else {
          hover.appendMarkdown(`🟡 **CovTest** — covered by test assertions only  \n\n`);
      }

      hover.appendMarkdown(`---\n`);
      hover.appendMarkdown(`[$(graph) Click to Generate Proof Coverage Report](command:proofpulse.getProofReport)`);

      covTestGutterOpts.push({
        range: new vscode.Range(i, 0, i, 0),
        hoverMessage: hover,
      });
    }
  }

  // Inline decorations — ranges only, no hover
  const uncoveredInlineRanges: vscode.Range[] = [];
  const covTestInlineRanges: vscode.Range[] = [];

  for (const node of nodes) {
    if (node.covStatus === CovStatus.Uncovered) {
      uncoveredInlineRanges.push(nodeToRange(node));
    } else if (node.covStatus === CovStatus.CovTest) {
      covTestInlineRanges.push(nodeToRange(node));
    }
  }

  editor.setDecorations(types.uncoveredGutter, uncoveredGutterOpts);
  editor.setDecorations(types.covTestGutter, covTestGutterOpts);
  editor.setDecorations(types.uncoveredInline, uncoveredInlineRanges);
  editor.setDecorations(types.covTestInline, covTestInlineRanges);
}

export function clearDecorations(editor: vscode.TextEditor): void {
  if (currentTypes) {
    editor.setDecorations(currentTypes.uncoveredGutter, []);
    editor.setDecorations(currentTypes.covTestGutter, []);
    editor.setDecorations(currentTypes.uncoveredInline, []);
    editor.setDecorations(currentTypes.covTestInline, []);
    disposeCurrentTypes();
  }
}

function disposeCurrentTypes(): void {
  if (currentTypes) {
    currentTypes.uncoveredGutter.dispose();
    currentTypes.covTestGutter.dispose();
    currentTypes.uncoveredInline.dispose();
    currentTypes.covTestInline.dispose();
    currentTypes = null;
  }
}

function nodeToRange(node: Node): vscode.Range {
  return new vscode.Range(
    node.start.line, node.start.col,
    node.end.line, node.end.col,
  );
}
