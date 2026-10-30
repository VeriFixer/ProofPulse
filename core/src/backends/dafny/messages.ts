/**
 * Dafny verifier messages → language-neutral NodeKind.
 *
 * These strings match Dafny's text log output, so they stay strings; this is
 * the only place in ProofPulse that interprets them.
 */
import { NodeKind, QueryOutcome, UnitKind } from "../../report/coverage-report.js";
import { TokenType } from "../../types.js";
import { tokenTypeForKinds } from "../../node-kind.js";

enum MessageMatch {
  Contains = "contains",
  Equals = "equals",
}

interface MessageRule {
  match: MessageMatch;
  text: string;
  kind: NodeKind;
}

const rule = (text: string, kind: NodeKind, match = MessageMatch.Contains): MessageRule => ({ match, text, kind });

/**
 * Ordered rules; the first match wins. Call-site clauses come first: a message
 * that mentions a callee clause is a call regardless of anything else in it.
 */
export const DAFNY_MESSAGE_RULES: readonly MessageRule[] = [
  rule("ensures clause at", NodeKind.CallEnsures),
  rule("requires clause at", NodeKind.CallRequires),
  rule("this postcondition holds", NodeKind.Postcondition),
  rule("precondition always holds", NodeKind.Precondition),
  rule("ensures clause", NodeKind.Postcondition),
  rule("requires clause", NodeKind.Precondition),
  rule("assertion always holds", NodeKind.Assert),
  rule("loop invariant holds on entry", NodeKind.Invariant),
  rule("loop invariant is maintained by the loop", NodeKind.Invariant),
  rule("loop invariant always holds", NodeKind.Invariant),
  rule("loop invariant", NodeKind.Invariant, MessageMatch.Equals),
  rule("condition atom", NodeKind.Condition, MessageMatch.Equals),
  rule("index in range", NodeKind.ImplicitCheck),
  rule("target object is never null", NodeKind.ImplicitCheck),
  rule("array is never null", NodeKind.ImplicitCheck),
  rule("which is subject to definite-assignment rules, is always initialized at this return point", NodeKind.ImplicitCheck),
  rule("which is subject to definite-assignment rules, is always initialized here", NodeKind.ImplicitCheck),
  rule("decreases expression is bounded below by", NodeKind.ImplicitCheck),
  rule("value always satisfies the subset constraints of", NodeKind.ImplicitCheck),
  rule("an array element is in the enclosing context's modifies clause", NodeKind.ImplicitCheck),
  rule("sufficient reads clause to read array element", NodeKind.ImplicitCheck),
];

/**
 * An assert statement used as a fact by a later proof. Dafny reports it with
 * the range of the whole asserted expression, while the assertion itself is
 * checked (`assertion always holds`) with the ranges of the parts it splits the
 * expression into: each conjunct, without enclosing parentheses.
 */
export function isAssertStatement(message: string): boolean {
  return message === "assert statement";
}

/** Kind of one Dafny log message. Unrecognised messages are ordinary code. */
export function dafnyMessageKind(message: string): NodeKind {
  for (const r of DAFNY_MESSAGE_RULES) {
    const hit = r.match === MessageMatch.Equals ? message === r.text : message.includes(r.text);
    if (hit) return r.kind;
  }
  return NodeKind.Code;
}

/**
 * Token type of a node from all Dafny messages seen at its location.
 * Kept for callers and tests that classify raw Dafny messages directly.
 */
export function classifyNodeType(prooftexts: string[], isTopAssertion: boolean): TokenType {
  return tokenTypeForKinds(prooftexts.map(dafnyMessageKind), isTopAssertion);
}

const UNIT_KINDS: Readonly<Record<string, UnitKind>> = {
  "correctness": UnitKind.Correctness,
  "well-formedness": UnitKind.WellFormedness,
};

/** "correctness" / "well-formedness" from `Results for X (...)`. */
export function dafnyUnitKind(methodType: string): UnitKind {
  return UNIT_KINDS[methodType] ?? UnitKind.Other;
}

/**
 * Batch outcome names. Dafny prints Boogie's prover outcome names; older logs
 * and some tests use the VC outcome names (`Correct`, `Errors`, …).
 */
const OUTCOMES: Readonly<Record<string, QueryOutcome>> = {
  Valid: QueryOutcome.Valid,
  Correct: QueryOutcome.Valid,
  Invalid: QueryOutcome.Invalid,
  Errors: QueryOutcome.Invalid,
  TimeOut: QueryOutcome.TimeOut,
  TimedOut: QueryOutcome.TimeOut,
  OutOfMemory: QueryOutcome.OutOfMemory,
  OutOfResource: QueryOutcome.OutOfResource,
  Undetermined: QueryOutcome.Undetermined,
  Inconclusive: QueryOutcome.Undetermined,
  Bounded: QueryOutcome.Bounded,
  SolverException: QueryOutcome.Error,
};

export function dafnyOutcome(outcome: string): QueryOutcome {
  return OUTCOMES[outcome] ?? QueryOutcome.Error;
}

const DURATION_RE = /^(?:(\d+)\.)?(\d+):(\d{2}):(\d{2})(?:\.(\d{1,7}))?$/;

/** .NET TimeSpan text ("00:00:00.3731157") → milliseconds; undefined if unparseable. */
export function parseDafnyDuration(duration: string): number | undefined {
  const m = duration.trim().match(DURATION_RE);
  if (!m) return undefined;
  const [, days, hours, minutes, seconds, fraction] = m;
  const totalSeconds = ((Number(days ?? 0) * 24 + Number(hours)) * 60 + Number(minutes)) * 60 + Number(seconds);
  const ticks = totalSeconds * 1e7 + Number((fraction ?? "").padEnd(7, "0") || 0);
  return ticks / 1e4;
}
