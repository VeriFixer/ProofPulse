import YAML from "js-yaml";
import { Node, CallNode, TopNode } from "./node.js";
import { NodeData, TokenType, CovStatus } from "./types.js";

type ProofGraphYamlV1 = {
  version: 1;
  nodes: Array<
    NodeData & {
      assertionGroup?: string;
      extras?: Record<string, unknown>;
    }
  >;
  edges: {
    tops: Array<{
      id: string;
      provedBy: string[];
      proofUnused: string[];
    }>;
    calls: Array<{
      id: string;
      connections: string[];
    }>;
  };
};

export class ProofGraph {
  private nodes: Map<string, Node> = new Map();
  private topNodes: Set<TopNode> = new Set();
  private callNodes: Set<CallNode> = new Set();

  addNode(node: Node): void {
    const id = node.getId();
    if (this.nodes.has(id)) return;

    this.nodes.set(id, node);
    if (node instanceof TopNode) this.topNodes.add(node);
    if (node instanceof CallNode) this.callNodes.add(node);
  }

  removeNode(id: string): boolean {
    const node = this.nodes.get(id);
    if (!node) return false;
    this.nodes.delete(id);
    if (node instanceof TopNode) this.topNodes.delete(node);
    if (node instanceof CallNode) this.callNodes.delete(node);

    for (const c of Array.from(this.callNodes)) {
      c.connections.delete(node);
    }

    for (const t of Array.from(this.topNodes)) {
      t.provedBy.delete(node);
      t.proofUnused.delete(node);
    }

    return true;
  }

  getNode(id: string): Node | undefined {
    return this.nodes.get(id);
  }

  hasNode(id: string): boolean {
    return this.nodes.has(id);
  }

  getAllNodes(): Node[] {
    return Array.from(this.nodes.values());
  }

  getAllTopNodes(): TopNode[] {
    return Array.from(this.topNodes);
  }

  getAllCallNodes(): CallNode[] {
    return Array.from(this.callNodes);
  }

  findNodesByPredicate(pred: (n: Node) => boolean): Node[] {
    return Array.from(this.nodes.values()).filter(pred);
  }

  addTopNode(top: TopNode): void {
    this.addNode(top);
  }

  removeTopNode(id: string): boolean {
    const node = this.getNode(id);
    if (!node || !(node instanceof TopNode)) return false;
    return this.removeNode(id);
  }

  connectCall(callId: string, targetId: string): boolean {
    const call = this.getNode(callId);
    const target = this.getNode(targetId);
    if (!call || !(call instanceof CallNode) || !target) return false;
    return call.addConnection(target);
  }

  addProvedBy(topId: string, proverId: string): boolean {
    const top = this.getNode(topId);
    const prover = this.getNode(proverId);
    if (!top || !(top instanceof TopNode) || !prover) return false;
    top.provedBy.add(prover);
    return true;
  }

  markProofUnused(topId: string, nodeId: string): boolean {
    const top = this.getNode(topId);
    const node = this.getNode(nodeId);
    if (!top || !(top instanceof TopNode) || !node) return false;
    top.proofUnused.add(node);
    return true;
  }

  clear(): void {
    this.nodes.clear();
    this.topNodes.clear();
    this.callNodes.clear();
  }

  toYAML(): string {
    const nodes: ProofGraphYamlV1["nodes"] = [];
    for (const node of this.nodes.values()) {
      const extras: Record<string, unknown> = {};
      const maybeAny = node as any;
      for (const k of ["batchIndex", "batchOutcome", "batchDuration", "batchResourceCount"]) {
        if (maybeAny[k] !== undefined) extras[k] = maybeAny[k];
      }

      nodes.push({
        id: node.getId(),
        file: node.file,
        start: node.start,
        end: node.end,
        prooftext: node.prooftext,
        isTopAssertion: node.isTopAssertion,
        type: node.getType(),
        covStatus: node.getCovStatus(),
        covStatusInternal: node.getCovStatusInternal(),
        methodName: node.assertion_group,
        methodType: node.methodType,
        assertionGroup: node.assertion_group,
        extras: Object.keys(extras).length ? extras : undefined,
      });
    }

    const edges: ProofGraphYamlV1["edges"] = {
      tops: Array.from(this.topNodes).map((t) => ({
        id: t.getId(),
        provedBy: Array.from(t.provedBy).map((n) => n.getId()),
        proofUnused: Array.from(t.proofUnused).map((n) => n.getId()),
      })),
      calls: Array.from(this.callNodes).map((c) => ({
        id: c.getId(),
        connections: Array.from(c.connections).map((n) => n.getId()),
      })),
    };

    const doc: ProofGraphYamlV1 = { version: 1, nodes, edges };
    return YAML.dump(doc);
  }

  fromYAML(yamlStr: string): void {
    const data = YAML.load(yamlStr) as ProofGraphYamlV1;
    if (!data) return;
    if (typeof data !== "object" || Array.isArray(data) || (data as any).version !== 1) {
      throw new Error("Unsupported YAML format: expected ProofGraphYamlV1 with version: 1");
    }

    const list: Array<any> = data.nodes;
    this.clear();

    const idMap = new Map<string, string>();

    for (const item of list) {
      const group = item.methodName ?? item.assertionGroup ?? "";
      const methodType = item.methodType ?? (item.extras?.methodType as string | undefined) ?? "";
      const isTop = !!item.isTopAssertion;
      let node: Node;
      if (isTop) {
        node = new TopNode(item.file, item.start.line, item.start.col, item.end.line, item.end.col, item.prooftext, group, methodType);
      } else if (item.type === TokenType.Call) {
        node = new CallNode(item.file, item.start.line, item.start.col, item.end.line, item.end.col, item.prooftext, group, false, methodType);
      } else {
        node = new Node(item.file, item.start.line, item.start.col, item.end.line, item.end.col, item.prooftext, group, !!item.isTopAssertion, methodType);
      }

      if (item.extras && typeof item.extras === "object") {
        Object.assign(node as any, item.extras);
      }

      if (typeof item.id === "string") {
        idMap.set(item.id, node.getId());
      }

      node.setCovStatus(item.covStatus ?? CovStatus.Uncovered);
      node.setCovStatusInternal(item.covStatusInternal ?? CovStatus.Uncovered);

      this.addNode(node);
    }

    const resolveId = (id: string) => idMap.get(id) ?? id;

    for (const topEdge of data.edges.tops) {
      const topId = resolveId(topEdge.id);
      for (const proverId of topEdge.provedBy) {
        this.addProvedBy(topId, resolveId(proverId));
      }
      for (const unusedId of topEdge.proofUnused) {
        this.markProofUnused(topId, resolveId(unusedId));
      }
    }

    for (const callEdge of data.edges.calls) {
      const callId = resolveId(callEdge.id);
      for (const conn of callEdge.connections ?? []) {
        this.connectCall(callId, resolveId(conn));
      }
    }
  }
}
