import { Node } from "./node.js";
import { NodeData } from "./types.js";

export interface BFSResult {
  node: Node;
  depth: number;
}

export interface ProofGraphJSON {
  nodes: NodeData[];
  topNodeIds: string[];
  edges: { from: string; to: string }[];
}

export class ProofGraph {
  private nodes: Map<string, Node>;
  private topNodes: Map<string, Node>;

  constructor() {
    this.nodes = new Map();
    this.topNodes = new Map();
  }

  addNode(node: Node): void {
    this.nodes.set(node.id, node);
  }

  getNode(id: string): Node | undefined {
    return this.nodes.get(id);
  }

  hasNode(id: string): boolean {
    return this.nodes.has(id);
  }

  addTopNode(node: Node): void {
    this.topNodes.set(node.id, node);
  }

  getTopNode(id: string): Node | undefined {
    return this.topNodes.get(id);
  }

  hasTopNode(id: string): boolean {
    return this.topNodes.has(id);
  }

  addEdge(fromId: string, toId: string): void {
    const from = this.getNode(fromId);
    const to = this.getNode(toId);
    if (!from || !to) {
      throw new Error(`Invalid edge: ${fromId} -> ${toId}`);
    }
    from.connectTo(to);
  }

  getAllNodes(): Node[] {
    return Array.from(this.nodes.values());
  }

  getAllTopNodes(): Node[] {
    return Array.from(this.topNodes.values());
  }

  getBFSNeighbors(
    key: string,
    isProvedBy: boolean,
    getAll: boolean = false,
    maxDepth?: number,
  ): BFSResult[] | null {
    if (!this.hasNode(key)) {
      return null;
    }

    // Negative maxDepth treated as 0 (unlimited)
    const effectiveMaxDepth = (maxDepth != null && maxDepth > 0) ? maxDepth : 0;

    const token = this.getNode(key)!;
    const results: BFSResult[] = [];
    const queue: { node: Node; depth: number }[] = [{ node: token, depth: 0 }];
    const visited = new Set<string>([token.id]);

    while (queue.length > 0) {
      const { node, depth } = queue.shift()!;
      let targetSet: Iterable<Node>;
      if (getAll) {
        targetSet = new Set([...node.provedBy, ...node.proves]);
      } else {
        targetSet = isProvedBy ? node.provedBy : node.proves;
      }
      const nextDepth = depth + 1;
      for (const pred of targetSet) {
        if (visited.has(pred.id)) {
          continue;
        }
        visited.add(pred.id);
        results.push({ node: pred, depth: nextDepth });
        if (effectiveMaxDepth === 0 || nextDepth < effectiveMaxDepth) {
          queue.push({ node: pred, depth: nextDepth });
        }
      }
    }
    return results;
  }

  toJSON(): ProofGraphJSON {
    const nodes: NodeData[] = this.getAllNodes().map((n) => n.toJSON());
    const topNodeIds: string[] = this.getAllTopNodes().map((n) => n.id);
    const edges: { from: string; to: string }[] = [];
    for (const node of this.getAllNodes()) {
      for (const child of node.provedBy) {
        edges.push({ from: node.id, to: child.id });
      }
    }
    return { nodes, topNodeIds, edges };
  }

  static fromJSON(data: ProofGraphJSON): ProofGraph {
    const graph = new ProofGraph();
    for (const nd of data.nodes) {
      graph.addNode(Node.fromJSON(nd));
    }
    for (const id of data.topNodeIds) {
      const node = graph.getNode(id);
      if (node) {
        graph.addTopNode(node);
      }
    }
    for (const edge of data.edges) {
      graph.addEdge(edge.from, edge.to);
    }
    return graph;
  }
}
