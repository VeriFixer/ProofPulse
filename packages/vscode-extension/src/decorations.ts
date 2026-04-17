import * as vscode from "vscode";
import { CovStatus, Node } from "@proofpulse/core";

export const uncoveredGutter = vscode.window.createTextEditorDecorationType({
  isWholeLine: true,
  backgroundColor: "rgba(255, 0, 0, 0.08)",
  overviewRulerColor: "rgba(255, 0, 0, 0.6)",
  overviewRulerLane: vscode.OverviewRulerLane.Left,
});

export const covTestGutter = vscode.window.createTextEditorDecorationType({
  isWholeLine: true,
  backgroundColor: "rgba(0, 120, 255, 0.08)",
  overviewRulerColor: "rgba(0, 120, 255, 0.6)",
  overviewRulerLane: vscode.OverviewRulerLane.Left,
});

export const uncoveredInline = vscode.window.createTextEditorDecorationType({
  color: "rgba(255, 80, 80, 1)",
});

export const covTestInline = vscode.window.createTextEditorDecorationType({
  color: "rgba(80, 160, 255, 1)",
});

const allTypes = [uncoveredGutter, covTestGutter, uncoveredInline, covTestInline];

export function applyDecorations(
  editor: vscode.TextEditor,
  lineStatus: CovStatus[],
  nodes: Node[],
): void {
  const uncoveredLines: vscode.Range[] = [];
  const covTestLines: vscode.Range[] = [];

  for (let i = 0; i < lineStatus.length; i++) {
    const status = lineStatus[i];
    if (status === CovStatus.Uncovered) {
      uncoveredLines.push(new vscode.Range(i, 0, i, 0));
    } else if (status === CovStatus.CovTest) {
      covTestLines.push(new vscode.Range(i, 0, i, 0));
    }
  }

  const uncoveredRanges: vscode.Range[] = [];
  const covTestRanges: vscode.Range[] = [];

  for (const node of nodes) {
    if (node.covStatus === CovStatus.Uncovered) {
      uncoveredRanges.push(nodeToRange(node));
    } else if (node.covStatus === CovStatus.CovTest) {
      covTestRanges.push(nodeToRange(node));
    }
  }

  editor.setDecorations(uncoveredGutter, uncoveredLines);
  editor.setDecorations(covTestGutter, covTestLines);
  editor.setDecorations(uncoveredInline, uncoveredRanges);
  editor.setDecorations(covTestInline, covTestRanges);
}

export function clearDecorations(editor: vscode.TextEditor): void {
  for (const t of allTypes) {
    editor.setDecorations(t, []);
  }
}

function nodeToRange(node: Node): vscode.Range {
  return new vscode.Range(
    node.start.line, node.start.col,
    node.end.line, node.end.col,
  );
}
