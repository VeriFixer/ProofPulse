import * as vscode from "vscode";
import { assertNever, CovStatus, flaggedExpressions, ProofNode, spanEndCol, TokenType, vacuityExplanation } from "@proofpulse/core";

interface DecorationTypes {
  uncoveredInline: vscode.TextEditorDecorationType;
  covTestInline: vscode.TextEditorDecorationType;
  vacuousInline: vscode.TextEditorDecorationType;
}

/** Module-level reference to current decoration types so clearDecorations can dispose them. */
let currentTypes: DecorationTypes | null = null;

/** Type-aware explanation for Uncovered status */
function uncoveredExplanation(type: TokenType): string {
  switch (type) {
    case TokenType.Postcondition: return "Postcondition not proven by any code path.";
    case TokenType.Precondition: return "Precondition not used in any proof obligation.";
    case TokenType.AssertionManual: return "Manual assertion not covered by proof dependencies.";
    case TokenType.LoopInvariant: return "Loop invariant not covered by proof dependencies.";
    case TokenType.CodeLine: return "Code line not contributing to any proof obligation.";
    case TokenType.Condition: return "The proof holds whichever way this condition part evaluates: it decides behaviour the contract leaves open.";
    case TokenType.AssertionAutomatic:
    case TokenType.Call:
    case TokenType.Assume:
    case TokenType.Axiom:
    case TokenType.Lemma:
    case TokenType.Undefined:
      return "Not covered by any proof path.";
    default: return assertNever(type, "token type");
  }
}

/** Type-aware explanation for CovTest status */
function covTestExplanation(type: TokenType): string {
  switch (type) {
    case TokenType.Postcondition: return "Postcondition not used in calling code (potentially unused method).";
    case TokenType.Precondition: return "Precondition only used in calling tests, unnecessary to prove postconditions.";
    case TokenType.CodeLine: return "Code used only by test assertions, not by postcondition proofs.";
    case TokenType.Condition: return "Condition part used only by test assertions, not by postcondition proofs.";
    case TokenType.AssertionManual: return "Assertion covered only by test paths, not postcondition proofs.";
    case TokenType.LoopInvariant: return "Loop invariant covered only by test paths, not postcondition proofs.";
    case TokenType.AssertionAutomatic:
    case TokenType.Call:
    case TokenType.Assume:
    case TokenType.Axiom:
    case TokenType.Lemma:
    case TokenType.Undefined:
      return "Covered only by test/non-postcondition assertions.";
    default: return assertNever(type, "token type");
  }
}

/** Explanation for a flagged node, by its status. */
function nodeExplanation(n: ProofNode): string {
  switch (n.covStatus) {
    case CovStatus.Vacuous: return vacuityExplanation(n.vacuity);
    case CovStatus.Uncovered: return uncoveredExplanation(n.getType());
    case CovStatus.CovTest: return covTestExplanation(n.getType());
    case CovStatus.CovComplete: return "";
    default: return assertNever(n.covStatus, "coverage status");
  }
}

const STATUS_ICON: Record<CovStatus, string> = {
  [CovStatus.Vacuous]: "🟣",
  [CovStatus.Uncovered]: "🔴",
  [CovStatus.CovTest]: "🟡",
  [CovStatus.CovComplete]: "",
};

/**
 * Only the flagged expressions are coloured: no gutter icons or scrollbar
 * marks, which would clash with the Dafny extension's own.
 */
export function createDecorationTypes(opacity: number): DecorationTypes {
  const inline = (rgb: string): vscode.DecorationRenderOptions => ({
    backgroundColor: `rgba(${rgb}, ${opacity})`,
    border: `1px solid rgba(${rgb}, 0.55)`,
    borderRadius: "2px",
  });
  return {
    uncoveredInline: vscode.window.createTextEditorDecorationType(inline("255, 0, 0")),
    covTestInline: vscode.window.createTextEditorDecorationType(inline("255, 200, 0")),
    vacuousInline: vscode.window.createTextEditorDecorationType({
      ...inline("150, 80, 255"),
      textDecoration: "underline wavy rgba(150, 80, 255, 0.9)",
    }),
  };
}

export function applyDecorations(
  editor: vscode.TextEditor,
  nodes: ProofNode[],
  opacity: number,
  showImplicitChecks = false,
): void {
  // Dispose old decoration types before creating fresh ones
  disposeCurrentTypes();
  const types = createDecorationTypes(opacity);
  currentTypes = types;

  const doc = editor.document;

  /** Extract a readable code snippet for a node. Falls back to full line if range is too small. */
  function nodeSnippet(n: ProofNode): string {
    const range = nodeToRange(doc, n);
    let text = doc.getText(range).replace(/\s+/g, " ").trim();
    // If extracted text is too short (single char like "=" or ">"), use the full line
    if (text.length <= 2 && range.start.line < doc.lineCount) {
      text = doc.lineAt(range.start.line).text.trim();
    }
    return text.length > 60 ? text.slice(0, 57) + "..." : text;
  }

  function hoverFor(lineNodes: ProofNode[]): vscode.MarkdownString {
    const hover = new vscode.MarkdownString(undefined, true);
    hover.isTrusted = true;
    hover.supportHtml = true;
    for (const n of lineNodes) {
      hover.appendMarkdown(`${STATUS_ICON[n.covStatus]} \`${nodeSnippet(n)}\` *(Line ${n.start.line}:${n.start.col})*  \n`);
      hover.appendMarkdown(`${nodeExplanation(n)}  \n\n`);
    }
    hover.appendMarkdown(`---\n`);
    hover.appendMarkdown(`[$(graph) Click to Generate Proof Coverage Report](command:proofpulse.getProofReport)`);
    return hover;
  }

  const flagged = flaggedExpressions(nodes, { includeImplicit: showImplicitChecks });

  // One decoration per flagged expression, hover for that expression only
  const inlineOpts = new Map<CovStatus, vscode.DecorationOptions[]>();
  for (const n of flagged) {
    let opts = inlineOpts.get(n.covStatus);
    if (!opts) { opts = []; inlineOpts.set(n.covStatus, opts); }
    opts.push({ range: nodeToRange(doc, n), hoverMessage: hoverFor([n]) });
  }

  editor.setDecorations(types.uncoveredInline, inlineOpts.get(CovStatus.Uncovered) ?? []);
  editor.setDecorations(types.covTestInline, inlineOpts.get(CovStatus.CovTest) ?? []);
  editor.setDecorations(types.vacuousInline, inlineOpts.get(CovStatus.Vacuous) ?? []);
}

export function clearDecorations(editor: vscode.TextEditor): void {
  if (currentTypes) {
    editor.setDecorations(currentTypes.uncoveredInline, []);
    editor.setDecorations(currentTypes.covTestInline, []);
    editor.setDecorations(currentTypes.vacuousInline, []);
    disposeCurrentTypes();
  }
}

function disposeCurrentTypes(): void {
  if (currentTypes) {
    currentTypes.uncoveredInline.dispose();
    currentTypes.covTestInline.dispose();
    currentTypes.vacuousInline.dispose();
    currentTypes = null;
  }
}

/**
 * Node spans are 1-based, ending at the start of their last token; vscode
 * ranges are 0-based and end-exclusive.
 */
function nodeToRange(doc: vscode.TextDocument, node: ProofNode): vscode.Range {
  const endLine = Math.max(0, node.end.line - 1);
  const endText = endLine < doc.lineCount ? doc.lineAt(endLine).text : "";
  return new vscode.Range(
    Math.max(0, node.start.line - 1), Math.max(0, node.start.col - 1),
    endLine, spanEndCol(endText, node.end.col),
  );
}
