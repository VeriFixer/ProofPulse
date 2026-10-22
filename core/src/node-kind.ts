import { NodeKind, isCallKind } from "./report/coverage-report.js";
import { TokenType } from "./types.js";

const KIND_TOKEN_TYPES: Readonly<Record<NodeKind, TokenType>> = {
  [NodeKind.Precondition]: TokenType.Precondition,
  [NodeKind.Postcondition]: TokenType.Postcondition,
  [NodeKind.Assert]: TokenType.AssertionManual,
  [NodeKind.ImplicitCheck]: TokenType.AssertionAutomatic,
  [NodeKind.Assume]: TokenType.Assume,
  [NodeKind.Invariant]: TokenType.LoopInvariant,
  [NodeKind.CallRequires]: TokenType.Call,
  [NodeKind.CallEnsures]: TokenType.Call,
  [NodeKind.Axiom]: TokenType.Axiom,
  [NodeKind.Lemma]: TokenType.Lemma,
  [NodeKind.Code]: TokenType.CodeLine,
  [NodeKind.Other]: TokenType.CodeLine,
};

/**
 * Token type of a graph node from the kinds of every occurrence merged into it
 * (in order) and whether it is a proof goal.
 *
 * - any call-site occurrence makes it a Call;
 * - otherwise the first occurrence decides;
 * - code that is itself a goal is a check the verifier added (AssertionAutomatic).
 */
export function tokenTypeForKinds(kinds: readonly NodeKind[], isTop: boolean): TokenType {
  if (kinds.some(isCallKind)) return TokenType.Call;
  if (kinds.length === 0) return TokenType.Undefined;
  const first = kinds[0];
  if ((first === NodeKind.Code || first === NodeKind.Other) && isTop) return TokenType.AssertionAutomatic;
  return KIND_TOKEN_TYPES[first];
}

const TOKEN_TYPE_KINDS: Readonly<Record<TokenType, NodeKind>> = {
  [TokenType.Undefined]: NodeKind.Other,
  [TokenType.Precondition]: NodeKind.Precondition,
  [TokenType.Postcondition]: NodeKind.Postcondition,
  [TokenType.AssertionManual]: NodeKind.Assert,
  [TokenType.AssertionAutomatic]: NodeKind.ImplicitCheck,
  [TokenType.LoopInvariant]: NodeKind.Invariant,
  [TokenType.Call]: NodeKind.CallEnsures,
  [TokenType.CodeLine]: NodeKind.Code,
  [TokenType.Assume]: NodeKind.Assume,
  [TokenType.Axiom]: NodeKind.Axiom,
  [TokenType.Lemma]: NodeKind.Lemma,
};

/** A node kind that maps back to the given token type (used when loading graph YAML). */
export function nodeKindForTokenType(type: TokenType): NodeKind {
  return TOKEN_TYPE_KINDS[type];
}
