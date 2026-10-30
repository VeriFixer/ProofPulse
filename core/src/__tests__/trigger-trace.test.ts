import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { parseTriggerTrace, triggerSuppliers } from "../minimization/trigger-trace.js";

// Traces of the two fixtures, written by z3 4.12.1 (`trace=true`).
const trace = (name: string) => parseTriggerTrace(readFileSync(resolve(__dirname, "fixtures", `${name}.trace`), "utf-8"));

describe("trigger suppliers from z3's trace", () => {
  // aux$$id2 `f(a) = 5` only supplies the term f(a) that triggers the
  // quantifier of aux$$id1; z3's core is (aux$$id1).
  it("credits the fact that supplied the trigger term", () => {
    const t = trace("trigger-term-core");
    expect([...t.guards.keys()].sort()).toEqual(["aux$$id1", "aux$$id2"]);
    expect(triggerSuppliers(t, new Set(["aux$$id1"]))).toEqual(["aux$$id2"]);
  });

  it("credits nothing when the kept facts already supply the term", () => {
    expect(triggerSuppliers(trace("trigger-term-core"), new Set(["aux$$id1", "aux$$id2"]))).toEqual([]);
  });

  // z3's core is (aux$$id2): R(a) from `forall y {f(y)} :: R(y)`. Its trigger
  // term f(a) was created by instantiating aux$$id1 `forall x {g(x)} :: Q(f(x))`,
  // which matched on g(a) from aux$$id3. aux$$id4 plays no part.
  it("follows a trigger term back through the instantiation that created it", () => {
    expect(triggerSuppliers(trace("trigger-chain"), new Set(["aux$$id2"])).sort()).toEqual(["aux$$id1", "aux$$id3"]);
  });

  // Traces of Dafny queries (z3 4.12.1, names obfuscated by Dafny, no quantifier ids).
  // `requires forall x {:trigger F(x)} :: P(x)` (id7), `requires F(a) > 0` (id8),
  // `ensures P(a)` (id9): z3's core is (id7 id9).
  it("credits a Dafny precondition that only supplies a trigger term", () => {
    expect(triggerSuppliers(trace("dafny-trigger-term"), new Set(["aux$$assume$$id7", "aux$$assert$$id9"]))).toEqual(["aux$$assume$$id8"]);
  });

  // `requires forall x {:trigger G(x)} :: F(x) == G(x) + 1` (id10),
  // `requires forall x {:trigger F(x)} :: P(x)` (id11), `requires G(a) > 0` (id12),
  // `ensures P(a)` (id13): z3's core is (id11 id13). The instantiation of id10
  // on G(a) creates F(a), which triggers id11.
  it("follows a Dafny trigger chain back to the fact that started it", () => {
    expect(triggerSuppliers(trace("dafny-trigger-chain"), new Set(["aux$$assume$$id11", "aux$$assert$$id13"])).sort())
      .toEqual(["aux$$assume$$id10", "aux$$assume$$id12"]);
  });

  it("finds no matches in an empty trace", () => {
    expect(triggerSuppliers(parseTriggerTrace(""), new Set())).toEqual([]);
  });
});
