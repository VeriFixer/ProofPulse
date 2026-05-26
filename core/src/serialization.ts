import { ProofGraph } from "./proof-graph.js";

/**
 * Serialize a ProofGraph to YAML.
 */
export function serializeProofGraph(graph: ProofGraph): string {
  return graph.toYAML();
}

/**
 * Deserialize a YAML string back into a ProofGraph.
 */
export function deserializeProofGraph(yaml: string): ProofGraph {
  const graph = new ProofGraph();
  graph.fromYAML(yaml);
  return graph;
}
