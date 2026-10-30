import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { parseProof } from "../proof.js";
import { flaggedExpressions } from "../flagged-expressions.js";
import { CovStatus } from "../types.js";

// Real Dafny log (proofpulse-ci image, --isolate-assertions, coverage report on) for fixtures/wellformedness.dfy.
const SOURCE = readFileSync(resolve(__dirname, "fixtures", "wellformedness.dfy"), "utf8");
const LOG = readFileSync(resolve(__dirname, "fixtures", "wellformedness.log"), "utf8");

/** Status of every flagged expression, keyed `line:col`. */
function flagged(): Map<string, CovStatus> {
  const proof = parseProof(SOURCE, LOG);
  return new Map(flaggedExpressions(proof.proofGraph.getAllNodes()).map(n => [`${n.start.line}:${n.start.col}`, n.getCovStatus()]));
}

describe("what checks rely on inherits the status of the clause holding them", () => {
  const statuses = flagged();

  it("a guard that makes a covered ensures well-defined is covered", () => {
    expect(statuses.has("9:12")).toBe(false);
    expect(statuses.has("9:17")).toBe(false);
  });

  it("a requires that makes an unused lemma's ensures well-defined is covered, like what proves it", () => {
    expect(statuses.get("25:11")).toBe(CovStatus.CovTest);
    expect(statuses.has("24:17")).toBe(false);
  });

  it("an invariant that only makes an uncovered invariant well-defined stays uncovered, as a whole", () => {
    expect(statuses.get("36:15")).toBe(CovStatus.Uncovered);
    expect(statuses.get("35:15")).toBe(CovStatus.Uncovered);
    expect(statuses.has("35:20")).toBe(false);
  });

  it("a requires that only serves a lemma call's precondition has the call's status", () => {
    expect(statuses.get("52:3")).toBe(CovStatus.CovTest);
    expect(statuses.get("49:12")).toBe(CovStatus.CovTest);
  });
});
