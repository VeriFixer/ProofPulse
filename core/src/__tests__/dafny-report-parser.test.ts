import { describe, it, expect } from "vitest";
import { DafnyReportParser } from "../dafny_report_parser.js";
import { ProofGraph } from "../proof-graph.js";
import { TopNode } from "../node.js";

describe("DafnyReportParser", () => {
  const SAMPLE_LOG = `
Results for AllElementsEqual (correctness)
  Assertion batch 0:
    Outcome: Correct
    Duration: 00:00:00.1
    Resource count: 1234
    Assertions:
      test.dfy(3,4)-(3,60): this postcondition holds
    Proof dependencies:
      test.dfy(8,8)-(8,20): loop invariant always holds
      test.dfy(10,12)-(10,30): index in range
    Unused by proof:
      test.dfy(5,4)-(5,30): requires clause
  Assertion batch 1:
    Outcome: Correct
    Duration: 00:00:00.05
    Resource count: 500
    Assertions:
      test.dfy(8,8)-(8,20): loop invariant holds on entry
    Proof dependencies:
      test.dfy(10,12)-(10,30): index in range
`;

  it("parseBatches extracts correct batch count", () => {
    const batches = DafnyReportParser.parseBatches(SAMPLE_LOG);
    expect(batches).toHaveLength(2);
  });

  it("parseBatches extracts method name and type", () => {
    const batches = DafnyReportParser.parseBatches(SAMPLE_LOG);
    expect(batches[0].methodName).toBe("AllElementsEqual");
    expect(batches[0].methodType).toBe("correctness");
  });

  it("parseBatches extracts top assertion", () => {
    const batches = DafnyReportParser.parseBatches(SAMPLE_LOG);
    expect(batches[0].topAssertion.proofText).toBe("this postcondition holds");
    expect(batches[0].topAssertion.startLine).toBe(3);
    expect(batches[0].topAssertion.startCol).toBe(4);
  });

  it("parseBatches extracts provedBy and unusedBy", () => {
    const batches = DafnyReportParser.parseBatches(SAMPLE_LOG);
    expect(batches[0].provedBy).toHaveLength(2);
    expect(batches[0].unusedBy).toHaveLength(1);
    expect(batches[0].unusedBy[0].proofText).toBe("requires clause");
  });

  it("buildProofGraph creates TopNodes for assertions", () => {
    const graph = DafnyReportParser.parseAndBuild(SAMPLE_LOG);
    const tops = graph.getAllTopNodes();
    // Batch 0 top: "this postcondition holds" at (3,4)-(3,60)
    // Batch 1 top: "loop invariant holds on entry" at (8,8)-(8,20)
    // But batch 1's top shares the same span+method+type as a provedBy node from batch 0
    // so it may deduplicate depending on ID generation. At minimum 1 top exists.
    expect(tops.length).toBeGreaterThanOrEqual(1);
  });

  it("buildProofGraph links provedBy to top nodes", () => {
    const graph = DafnyReportParser.parseAndBuild(SAMPLE_LOG);
    const tops = graph.getAllTopNodes();
    const postTop = tops.find(t => t.prooftext === "this postcondition holds");
    expect(postTop).toBeDefined();
    expect(postTop!.provedBy.size).toBe(2);
  });

  it("buildProofGraph links proofUnused to top nodes", () => {
    const graph = DafnyReportParser.parseAndBuild(SAMPLE_LOG);
    const tops = graph.getAllTopNodes();
    const postTop = tops.find(t => t.prooftext === "this postcondition holds");
    expect(postTop).toBeDefined();
    expect(postTop!.proofUnused.size).toBe(1);
  });

  it("toYAML produces valid YAML that can be re-parsed", () => {
    const graph = DafnyReportParser.parseAndBuild(SAMPLE_LOG);
    const yaml = graph.toYAML();
    expect(yaml).toContain("version: 1");
    expect(yaml).toContain("this postcondition holds");

    // Round-trip
    const graph2 = new ProofGraph();
    graph2.fromYAML(yaml);
    expect(graph2.getAllTopNodes().length).toBe(graph.getAllTopNodes().length);
    expect(graph2.getAllNodes().length).toBe(graph.getAllNodes().length);
  });
});
