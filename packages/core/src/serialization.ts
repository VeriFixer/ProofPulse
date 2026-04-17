import { ProofGraph, ProofGraphJSON } from "./proof-graph.js";

/**
 * Serialize a ProofGraph to canonical JSON (sorted keys for determinism).
 */
export function serializeProofGraph(graph: ProofGraph): string {
  const data = graph.toJSON();

  // Sort nodes by id
  const nodes = [...data.nodes].sort((a, b) => a.id.localeCompare(b.id));

  // Sort edges by from, then to
  const edges = [...data.edges].sort(
    (a, b) => a.from.localeCompare(b.from) || a.to.localeCompare(b.to),
  );

  // Sort topNodeIds
  const topNodeIds = [...data.topNodeIds].sort();

  const canonical: ProofGraphJSON = { nodes, topNodeIds, edges };
  return JSON.stringify(canonical, (_key: string, value: unknown) => {
    if (value !== null && typeof value === "object" && !Array.isArray(value)) {
      const sorted: Record<string, unknown> = {};
      for (const k of Object.keys(value as Record<string, unknown>).sort()) {
        sorted[k] = (value as Record<string, unknown>)[k];
      }
      return sorted;
    }
    return value;
  });
}

/**
 * Deserialize a JSON string back into a ProofGraph.
 */
export function deserializeProofGraph(json: string): ProofGraph {
  const data: ProofGraphJSON = JSON.parse(json);
  return ProofGraph.fromJSON(data);
}
