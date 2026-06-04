import YAML from "js-yaml";
import { ProofNode } from "./proof-node.js";
import { CovStatus, SourceLocation } from "./types.js";

export class ProofGraph {
  private nodes: Map<string, ProofNode> = new Map();

  getOrCreate(
    file: string,
    start: SourceLocation,
    end: SourceLocation,
    methodName: string,
    methodType: string,
    prooftext: string,
  ): ProofNode {
    const temp = new ProofNode(file, start, end, methodName, methodType, prooftext);
    const id = temp.getId();
    const existing = this.nodes.get(id);
    if (existing) {
      existing.addProoftext(prooftext);
      return existing;
    }
    this.nodes.set(id, temp);
    return temp;
  }

  addNode(node: ProofNode): void {
    const id = node.getId();
    if (!this.nodes.has(id)) {
      this.nodes.set(id, node);
    }
  }

  addTopNode(node: ProofNode): void {
    this.addNode(node);
    node.addRole("isTop");
  }

  getAllTopNodes(): ProofNode[] {
    return Array.from(this.nodes.values()).filter((n) => n.roles.isTop);
  }

  getAllCallNodes(): ProofNode[] {
    return Array.from(this.nodes.values()).filter((n) => n.roles.isCall);
  }

  getAllNodes(): ProofNode[] {
    return Array.from(this.nodes.values());
  }

  getNode(id: string): ProofNode | undefined {
    return this.nodes.get(id);
  }

  hasNode(id: string): boolean {
    return this.nodes.has(id);
  }

  addProvedBy(topId: string, proverId: string): boolean {
    if (topId === proverId) return false;
    const top = this.nodes.get(topId);
    const prover = this.nodes.get(proverId);
    if (!top || !prover) return false;
    top.provedBy.add(prover);
    return true;
  }

  markProofUnused(topId: string, nodeId: string): boolean {
    const top = this.nodes.get(topId);
    const node = this.nodes.get(nodeId);
    if (!top || !node) return false;
    top.proofUnused.add(node);
    return true;
  }

  connectCall(callId: string, targetId: string): boolean {
    const call = this.nodes.get(callId);
    const target = this.nodes.get(targetId);
    if (!call || !target) return false;
    call.connections.add(target);
    return true;
  }

  removeNode(id: string): boolean {
    const node = this.nodes.get(id);
    if (!node) return false;
    this.nodes.delete(id);

    // Clean up references in other nodes' sets
    for (const n of this.nodes.values()) {
      n.provedBy.delete(node);
      n.proofUnused.delete(node);
      n.connections.delete(node);
    }
    return true;
  }

  findNodesByPredicate(pred: (n: ProofNode) => boolean): ProofNode[] {
    return Array.from(this.nodes.values()).filter(pred);
  }

  /** Count how many top assertions reference this node as a prover. */
  getUsageCount(nodeId: string): number {
    const node = this.nodes.get(nodeId);
    if (!node) return 0;
    let count = 0;
    for (const top of this.nodes.values()) {
      if (top.provedBy.has(node)) count++;
    }
    return count;
  }

  /** Return distinct method|type contexts where the same file+span appears. */
  getMethodContexts(nodeId: string): string[] {
    const node = this.nodes.get(nodeId);
    if (!node) return [];
    const span = `${node.start.line},${node.start.col}-${node.end.line},${node.end.col}`;
    const contexts: Set<string> = new Set();
    for (const n of this.nodes.values()) {
      if (n.file !== node.file) continue;
      const nSpan = `${n.start.line},${n.start.col}-${n.end.line},${n.end.col}`;
      if (nSpan === span) {
        contexts.add(`${n.methodName}|${n.methodType}`);
      }
    }
    return Array.from(contexts);
  }

  /** Count how many distinct top assertions this node proves. */
  getTopAssertionCount(nodeId: string): number {
    return this.getUsageCount(nodeId);
  }

  /** Return nodes this call node connects to (call targets). */
  getConnections(nodeId: string): ProofNode[] {
    const node = this.nodes.get(nodeId);
    if (!node) return [];
    return Array.from(node.connections);
  }

  /** Return call nodes that connect to this node (called by). */
  getCalledBy(nodeId: string): ProofNode[] {
    const node = this.nodes.get(nodeId);
    if (!node) return [];
    const result: ProofNode[] = [];
    for (const n of this.nodes.values()) {
      if (n.connections.has(node)) {
        result.push(n);
      }
    }
    return result;
  }

  clear(): void {
    this.nodes.clear();
  }

  toYAML(): string {
    const nodes = Array.from(this.nodes.values()).map((node) => ({
      locationId: node.locationId,
      file: node.file,
      start: node.start,
      end: node.end,
      methodName: node.methodName,
      methodType: node.methodType,
      prooftexts: node.prooftexts,
      roles: { ...node.roles },
      type: node.getType(),
      usedByNumber : this.getTopAssertionCount(node.getId()),
      topMeta: node.topMeta ?? null,
      covStatus: node.covStatus,
      covStatusInternal: node.covStatusInternal,
    }));

    const edges: {
      provedBy: Array<{ top: string; provers: string[] }>;
      proofUnused: Array<{ top: string; unused: string[] }>;
      connections: Array<{ call: string; targets: string[] }>;
    } = { provedBy: [], proofUnused: [], connections: [] };

    for (const node of this.nodes.values()) {
      if (node.provedBy.size > 0) {
        edges.provedBy.push({
          top: node.locationId,
          provers: Array.from(node.provedBy).map((n) => n.locationId),
        });
      }
      if (node.proofUnused.size > 0) {
        edges.proofUnused.push({
          top: node.locationId,
          unused: Array.from(node.proofUnused).map((n) => n.locationId),
        });
      }
      if (node.connections.size > 0) {
        edges.connections.push({
          call: node.locationId,
          targets: Array.from(node.connections).map((n) => n.locationId),
        });
      }
    }

    const doc = { version: 2, nodes, edges };
    return YAML.dump(doc);
  }

  fromYAML(yamlStr: string): void {
    const data = YAML.load(yamlStr) as any;
    if (!data || typeof data !== "object" || data.version !== 2) {
      throw new Error("Unsupported YAML version — only version 2 is supported");
    }

    this.clear();

    // Reconstruct nodes
    for (const item of data.nodes) {
      const node = new ProofNode(
        item.file,
        item.start,
        item.end,
        item.methodName,
        item.methodType,
        item.prooftexts[0] ?? "",
      );

      // Add remaining prooftexts
      for (let i = 1; i < item.prooftexts.length; i++) {
        node.addProoftext(item.prooftexts[i]);
      }

      // Restore roles
      if (item.roles) {
        if (item.roles.isTop) node.addRole("isTop");
        if (item.roles.isCall) node.addRole("isCall");
        if (item.roles.isProvedBy) node.addRole("isProvedBy");
        if (item.roles.isUnused) node.addRole("isUnused");
      }

      // Restore topMeta
      if (item.topMeta) {
        node.topMeta = item.topMeta;
      }

      // Restore coverage status
      node.setCovStatus(item.covStatus ?? CovStatus.Uncovered);
      node.setCovStatusInternal(item.covStatusInternal ?? CovStatus.Uncovered);

      this.addNode(node);
    }

    // Reconstruct edges
    if (data.edges) {
      if (data.edges.provedBy) {
        for (const edge of data.edges.provedBy) {
          for (const proverId of edge.provers) {
            this.addProvedBy(edge.top, proverId);
          }
        }
      }
      if (data.edges.proofUnused) {
        for (const edge of data.edges.proofUnused) {
          for (const unusedId of edge.unused) {
            this.markProofUnused(edge.top, unusedId);
          }
        }
      }
      if (data.edges.connections) {
        for (const edge of data.edges.connections) {
          for (const targetId of edge.targets) {
            this.connectCall(edge.call, targetId);
          }
        }
      }
    }
  }
}
