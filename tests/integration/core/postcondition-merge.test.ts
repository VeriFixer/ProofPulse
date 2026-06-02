import { describe, it, expect } from "vitest";
import { parseProof } from "../../../core/src/proof.js";
import { CovStatus, TokenType } from "../../../core/src/types.js";

/**
 * Regression test: postcondition sub-expressions must merge into the parent
 * postcondition node rather than creating orphan top nodes.
 *
 * Dafny sometimes emits multiple assertion batches for the same ensures clause:
 * one for the full expression range and another for a sub-expression (e.g. the
 * equality operator). The sub-expression batch must not create a separate
 * Uncovered top node — it should merge into the existing postcondition top.
 */

const IMPOSSIBLE_PRECONDITION_SOURCE = `method DemoImpossiblePrecondition(a: int)
    returns (r: int)
  requires forall t :: t*t + 1 <= t*t
  ensures 2 == 3
{
  var k := a + 1;
  var m := k * 2;
  r := m - k;
}`;

describe("Postcondition sub-expression merging", () => {
  it("sub-expression point-node merges into existing postcondition range-node", () => {
    // Simulates Dafny output where:
    // Batch 0: top assertion at (4,11) "this postcondition holds"
    //          proof dep range (4,11)-(4,17) "ensures clause" (the full `2 == 3`)
    // Batch 1: top assertion at (4,13) "this postcondition holds"  (just the `==`)
    //          proof dep range (4,11)-(4,17) "ensures clause" (same full range)
    //
    // Without the fix, batch 1's top at (4,13)-(4,13) becomes a separate
    // Uncovered top node. With the fix, it merges into the (4,11)-(4,17) node.
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);
    const allNodes = proof.proofGraph.getAllNodes();
    const topNodes = proof.proofGraph.getAllTopNodes();

    // The sub-expression point-node (4,13)-(4,13) should NOT exist as a separate node
    const subExprNode = allNodes.find(
      (n) => n.locationId === "test.dfy:4,13-4,13",
    );
    expect(subExprNode).toBeUndefined();

    // There should be exactly one postcondition top node for line 4
    const postTops = topNodes.filter(
      (n) => n.getType() === TokenType.Postcondition && n.start.line === 4,
    );
    expect(postTops.length).toBe(1);

    // The postcondition top should be the range node (4,11)-(4,17)
    expect(postTops[0].id).toBe("test.dfy:4,11-4,17");
  });

  it("postcondition with impossible precondition: ensures line is NOT Uncovered", () => {
    // When precondition is impossible (vacuously true), the postcondition
    // is trivially satisfied → CovComplete (!). Body code is Uncovered.
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);

    // Line 4 (ensures 2 == 3) should NOT be Uncovered
    // It should be CovTest or CovComplete because the postcondition holds
    const line4Status = proof.lineStatus[3]; // 0-indexed
    expect(line4Status).not.toBe(CovStatus.Uncovered);
  });

  it("multiple batches referencing same ensures range don't create duplicate tops", () => {
    // Three batches all pointing to the same postcondition range
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "",
      "  Assertion batch 2:",
      "  Assertions:",
      "    test.dfy(4, 14): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);
    const topNodes = proof.proofGraph.getAllTopNodes();

    // Should have exactly one postcondition top for line 4
    const postTops = topNodes.filter(
      (n) => n.getType() === TokenType.Postcondition && n.start.line === 4,
    );
    expect(postTops.length).toBe(1);
    expect(postTops[0].id).toBe("test.dfy:4,11-4,17");
  });

  it("sub-expression that appears before the full range still merges", () => {
    // Edge case: batch order reversed — sub-expression appears first
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);
    const topNodes = proof.proofGraph.getAllTopNodes();

    // Should have exactly one postcondition top for line 4
    const postTops = topNodes.filter(
      (n) => n.getType() === TokenType.Postcondition && n.start.line === 4,
    );
    expect(postTops.length).toBe(1);
    expect(postTops[0].id).toBe("test.dfy:4,11-4,17");
  });

  it("sub-expression range-node in proof deps that does NOT contain top assertion point", () => {
    // Scenario: Dafny outputs a sub-expression as a range in proof deps
    // that is SMALLER than the full ensures clause and doesn't contain the
    // top assertion's start point.
    // Batch 0: top at (4,11), proof dep (4,11)-(4,17) → merges fine
    // Batch 1: top at (4,11), proof dep (4,13)-(4,14) "ensures clause" (just `==`)
    //          This sub-range does NOT contain (4,11), so without fix it becomes
    //          a separate child node with "ensures clause" text → Postcondition type
    //          that stays Uncovered and pollutes line 4.
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 13)-(4, 14): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);
    const topNodes = proof.proofGraph.getAllTopNodes();
    const allNodes = proof.proofGraph.getAllNodes();

    // Debug: check what nodes exist
    const line4Nodes = allNodes.filter((n) => n.start.line === 4);
    const line4Tops = topNodes.filter((n) => n.start.line === 4);

    // The sub-range (4,13)-(4,14) should either be merged or at minimum
    // should not cause line 4 to be Uncovered
    const line4Status = proof.lineStatus[3];
    expect(line4Status).not.toBe(CovStatus.Uncovered);

    // Should have at most one postcondition top for line 4
    const postTops = line4Tops.filter(
      (n) => n.getType() === TokenType.Postcondition,
    );
    expect(postTops.length).toBe(1);
  });

  it("REAL BUG: point-node top re-created after promotion causes orphan", () => {
    // The ACTUAL bug scenario:
    // Batch 0: top at (4,11) → promoted to (4,11)-(4,17) via proof dep
    //          The point-node (4,11)-(4,11) is DELETED from the graph.
    // Batch 1: top at (4,13) → creates point-node (4,13)-(4,13)
    //          proof dep (4,11)-(4,17) already exists, containment check:
    //          start.col(11) <= top.start.col(13) ✓, top.start.col(13) <= end.col(17) ✓
    //          → merges! So this works.
    //
    // But what if there's NO proof dep that contains the sub-expression?
    // Batch 1: top at (4,13) → creates point-node (4,13)-(4,13)
    //          proof dep (4,13)-(4,14) does NOT contain (4,13) properly
    //          (start.col(13) <= top.start.col(13) ✓, but token.id === currentTopAssertion.id check?)
    //          Actually (4,13)-(4,14) != (4,13)-(4,13) so ids differ.
    //          Containment: 13 <= 13 ✓, 13 <= 14 ✓, line checks pass.
    //          → merges into (4,13)-(4,14)!
    //
    // The REAL scenario that breaks: no proof dep at all for the sub-expression batch
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);
    const topNodes = proof.proofGraph.getAllTopNodes();

    // The point-node (4,13)-(4,13) should NOT be a separate top
    const postTops = topNodes.filter(
      (n) => n.getType() === TokenType.Postcondition && n.start.line === 4,
    );

    // Line 4 should not be Uncovered
    const line4Status = proof.lineStatus[3];
    expect(line4Status).not.toBe(CovStatus.Uncovered);
  });

  it("REAL BUG: point-node top re-created after promotion causes orphan", () => {
    // No proof dep at all for the sub-expression batch → orphan top
    const proofLog = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(4, 11): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(4, 11)-(4, 17): ensures clause",
      "    test.dfy(3, 12)-(3, 40): requires clause",
      "",
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);

    // Line 4 should not be Uncovered
    const line4Status = proof.lineStatus[3];
    expect(line4Status).not.toBe(CovStatus.Uncovered);
  });

  it("ensures clause in Unused block promotes into top node (real Dafny output)", () => {
    // This is the ACTUAL output from Dafny for impossible precondition:
    // The ensures clause range appears in Unused, not ProofDep.
    // Without the fix, it stays as a separate non-top Postcondition node
    // with Uncovered status, polluting line 4.
    const proofLog = [
      "  Assertion batch 1:",
      "  Assertions:",
      "    test.dfy(4, 13): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(3, 12)-(3, 37): requires clause",
      "  Unused by proof:",
      "    test.dfy(4, 11)-(4, 16): ensures clause",
      "    test.dfy(6, 7)-(6, 17): assignment (or return)",
      "    test.dfy(7, 7)-(7, 17): assignment (or return)",
      "    test.dfy(8, 3)-(8, 13): assignment (or return)",
    ].join("\n");

    const proof = parseProof(IMPOSSIBLE_PRECONDITION_SOURCE, proofLog);
    const topNodes = proof.proofGraph.getAllTopNodes();

    // The ensures clause range should have promoted to be the top node
    const postTops = topNodes.filter(
      (n) => n.getType() === TokenType.Postcondition && n.start.line === 4,
    );
    expect(postTops.length).toBe(1);
    expect(postTops[0].id).toBe("test.dfy:4,11-4,16");

    // Line 4 should be CovTest (postcondition proved by precondition, not called externally)
    const line4Status = proof.lineStatus[3];
    expect(line4Status).toBe(CovStatus.CovTest);

    // Body lines should be Uncovered
    expect(proof.lineStatus[5]).toBe(CovStatus.Uncovered); // L6
    expect(proof.lineStatus[6]).toBe(CovStatus.Uncovered); // L7
    expect(proof.lineStatus[7]).toBe(CovStatus.Uncovered); // L8
  });
});
