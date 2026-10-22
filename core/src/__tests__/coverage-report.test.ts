import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import {
  COVERAGE_REPORT_SCHEMA,
  CoverageReport,
  NodeKind,
  QueryOutcome,
  UnitKind,
  VerifierId,
} from "../report/coverage-report.js";
import { ReportValidationError, validateCoverageReport } from "../report/validate.js";
import { ReportFormat, parseCoverageReport, serializeCoverageReport } from "../report/io.js";
import { dafnyLogToReport } from "../backends/dafny/log-parser.js";
import { ProofGraph } from "../proof-graph.js";
import { TokenType } from "../types.js";

const SRC_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "..");

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

const arbPosition = fc.record({ line: fc.integer({ min: 1, max: 500 }), col: fc.integer({ min: 1, max: 120 }) });

/** A structurally valid report: every reference points at an existing id. */
const arbReport: fc.Arbitrary<CoverageReport> = fc
  .record({
    nodeCount: fc.integer({ min: 1, max: 12 }),
    sourceCount: fc.integer({ min: 1, max: 3 }),
  })
  .chain(({ nodeCount, sourceCount }) => {
    const nodeId = fc.integer({ min: 0, max: nodeCount - 1 }).map((i) => `n${i}`);
    const node = (i: number) =>
      fc.record({
        id: fc.constant(`n${i}`),
        kind: fc.constantFrom(...Object.values(NodeKind)),
        span: fc.record({
          file: fc.integer({ min: 0, max: sourceCount - 1 }).map((s) => `f${s}`),
          start: arbPosition,
          end: arbPosition,
        }),
        message: fc.string({ maxLength: 30 }),
      });
    const query = (u: number, q: number) =>
      fc.record({
        id: fc.constant(`u${u}q${q}`),
        index: fc.constant(q),
        outcome: fc.constantFrom(...Object.values(QueryOutcome)),
        resourceCount: fc.nat(),
        goals: fc.array(nodeId, { minLength: 1, maxLength: 2 }),
        used: fc.array(nodeId, { maxLength: 5 }),
        unused: fc.array(nodeId, { maxLength: 5 }),
      });
    return fc.record({
      schema: fc.constant(COVERAGE_REPORT_SCHEMA),
      tool: fc.record({ name: fc.constantFrom(...Object.values(VerifierId)) }),
      sources: fc.constant(Array.from({ length: sourceCount }, (_, i) => ({ id: `f${i}`, path: `file${i}.dfy` }))),
      nodes: fc.tuple(...Array.from({ length: nodeCount }, (_, i) => node(i))),
      units: fc.integer({ min: 0, max: 3 }).chain((unitCount) =>
        fc.tuple(
          ...Array.from({ length: unitCount }, (_, u) =>
            fc.record({
              id: fc.constant(`u${u}`),
              name: fc.constantFrom("Main", "Abs", "Max"),
              kind: fc.constantFrom(...Object.values(UnitKind)),
              queries: fc.integer({ min: 0, max: 3 }).chain((n) =>
                fc.tuple(...Array.from({ length: n }, (_, q) => query(u, q))),
              ),
            }),
          ),
        ),
      ),
    }) as fc.Arbitrary<CoverageReport>;
  });

// ---------------------------------------------------------------------------
// Property 2: round-trip
// ---------------------------------------------------------------------------

describe("Property 2: coverage report round-trip", () => {
  for (const format of [ReportFormat.Yaml, ReportFormat.Json]) {
    it(`parse(serialize(report)) equals report (${format})`, () => {
      fc.assert(
        fc.property(arbReport, (report) => {
          expect(parseCoverageReport(serializeCoverageReport(report, format))).toEqual(report);
        }),
        { numRuns: 100 },
      );
    });
  }
});

// ---------------------------------------------------------------------------
// Property 3: referential integrity
// ---------------------------------------------------------------------------

describe("Property 3: referential integrity", () => {
  it("every generated report validates", () => {
    fc.assert(fc.property(arbReport, (report) => {
      expect(() => validateCoverageReport(JSON.parse(JSON.stringify(report)))).not.toThrow();
    }));
  });

  it("a dangling reference is rejected with its path", () => {
    fc.assert(
      fc.property(
        arbReport.filter((r) => r.units.some((u) => u.queries.length > 0)),
        fc.constantFrom("goals", "used", "unused") as fc.Arbitrary<"goals" | "used" | "unused">,
        (report, field) => {
          const copy = JSON.parse(JSON.stringify(report)) as CoverageReport;
          const u = copy.units.findIndex((x) => x.queries.length > 0);
          copy.units[u].queries[0][field].push("missing-node");
          const k = copy.units[u].queries[0][field].length - 1;
          try {
            validateCoverageReport(copy);
            throw new Error("expected validation to fail");
          } catch (err) {
            expect(err).toBeInstanceOf(ReportValidationError);
            expect((err as ReportValidationError).path).toBe(`/units/${u}/queries/0/${field}/${k}`);
          }
        },
      ),
    );
  });

  it("rejects an unknown source in a node span", () => {
    const report = dafnyLogToReport(SAMPLE_LOG);
    report.nodes[0].span.file = "nope";
    expect(() => validateCoverageReport(report)).toThrow(/\/nodes\/0\/span\/file/);
  });

  it("rejects other schema versions", () => {
    const report = { ...dafnyLogToReport(SAMPLE_LOG), schema: "proofpulse-coverage/v0" };
    expect(() => validateCoverageReport(report)).toThrow(/unsupported schema/);
  });

  it("reads unknown node and unit kinds as Other", () => {
    const report = JSON.parse(JSON.stringify(dafnyLogToReport(SAMPLE_LOG)));
    report.nodes[0].kind = "future-kind";
    report.units[0].kind = "future-unit";
    const validated = validateCoverageReport(report);
    expect(validated.nodes[0].kind).toBe(NodeKind.Other);
    expect(validated.units[0].kind).toBe(UnitKind.Other);
  });
});

// ---------------------------------------------------------------------------
// Dafny adapter
// ---------------------------------------------------------------------------

const SAMPLE_LOG = `
Results for Caller (correctness)
  Assertion batch 1:
    Outcome: Valid
    Duration: 00:00:00.1234567
    Resource count: 1234
    Assertions:
      test.dfy(3,4)-(3,60): this postcondition holds
    Proof dependencies:
      test.dfy(8,8)-(8,20): ensures clause at test.dfy(20,10)-(20,25) from call
      test.dfy(10,12)-(10,30): index in range
    Unused by proof:
      test.dfy(5,4)-(5,30): requires clause

Results for Caller (well-formedness)
  Assertion batch 1:
    Outcome: Valid
    Duration: 00:00:00.01
    Resource count: 10
    Assertions:
      test.dfy(3,4)-(3,60): this postcondition holds
`;

describe("Dafny adapter", () => {
  const report = dafnyLogToReport(SAMPLE_LOG, { version: "4.11.1", minimized: true });

  it("produces one unit per results block, with Dafny's unit kinds", () => {
    expect(report.units.map((u) => [u.name, u.kind])).toEqual([
      ["Caller", UnitKind.Correctness],
      ["Caller", UnitKind.WellFormedness],
    ]);
  });

  it("maps a batch to a query with goals, used and unused", () => {
    const q = report.units[0].queries[0];
    const msg = (id: string) => report.nodes.find((n) => n.id === id)!.message;
    expect(q.outcome).toBe(QueryOutcome.Valid);
    expect(q.durationMs).toBeCloseTo(123.4567, 6);
    expect(q.goals.map(msg)).toEqual(["this postcondition holds"]);
    expect(q.used.map(msg)).toEqual(["ensures clause at test.dfy(20,10)-(20,25) from call", "index in range"]);
    expect(q.unused.map(msg)).toEqual(["requires clause"]);
  });

  it("classifies messages into node kinds", () => {
    const kind = (message: string) => report.nodes.find((n) => n.message === message)!.kind;
    expect(kind("this postcondition holds")).toBe(NodeKind.Postcondition);
    expect(kind("ensures clause at test.dfy(20,10)-(20,25) from call")).toBe(NodeKind.CallEnsures);
    expect(kind("index in range")).toBe(NodeKind.ImplicitCheck);
    expect(kind("requires clause")).toBe(NodeKind.Precondition);
  });

  it("links a call-site clause to the callee clause", () => {
    const call = report.nodes.find((n) => n.kind === NodeKind.CallEnsures)!;
    const target = report.nodes.find((n) => n.id === call.callTargets![0])!;
    expect(target.message).toBe("ensures clause");
    expect(target.kind).toBe(NodeKind.Postcondition);
    expect(target.span.start).toEqual({ line: 20, col: 10 });
  });

  it("shares one node per (location, message) across units", () => {
    const tops = report.nodes.filter((n) => n.message === "this postcondition holds");
    expect(tops).toHaveLength(1);
  });

  it("records tool information", () => {
    expect(report.tool).toMatchObject({ name: VerifierId.Dafny, version: "4.11.1", minimized: true });
  });

  it("graph skips non-proof units and marks call roles", () => {
    const graph = ProofGraph.fromReport(report);
    expect(graph.getAllNodes().every((n) => n.methodType === UnitKind.Correctness)).toBe(true);
    const call = graph.getAllCallNodes();
    expect(call).toHaveLength(1);
    expect(call[0].getType()).toBe(TokenType.Call);
    expect(graph.getConnections(call[0].getId())).toHaveLength(1);
  });

  it("graph YAML round-trips node types without per-occurrence kinds", () => {
    const graph = ProofGraph.fromReport(report);
    const reloaded = new ProofGraph();
    reloaded.fromYAML(graph.toYAML());
    expect(reloaded.getAllNodes().map((n) => n.getType())).toEqual(graph.getAllNodes().map((n) => n.getType()));
  });
});

// ---------------------------------------------------------------------------
// Property 5: no verifier-specific logic in the language-neutral core
// ---------------------------------------------------------------------------

describe("Property 5: core modules are verifier-neutral", () => {
  const CORE_MODULES = ["proof-graph.ts", "proof-node.ts", "coverage.ts", "node-kind.ts", "span-tree.ts"];
  const FORBIDDEN = [/dafny/i, /verus/i, /kani/i, /postcondition holds/, /clause at/, /\.dfy\b/];

  for (const file of CORE_MODULES) {
    it(`${file} has no verifier-specific strings`, () => {
      const text = fs.readFileSync(path.join(SRC_DIR, file), "utf8");
      for (const re of FORBIDDEN) {
        expect(text, `${file} matches ${re}`).not.toMatch(re);
      }
    });
  }
});
