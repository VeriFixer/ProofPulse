import { CovStatus, TokenType } from "./types.js";
import { Node } from "./node.js";
import { ProofGraph } from "./proof-graph.js";

export interface SpanEntry {
  file: string;
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  message: string;
}

export type SpanMap = SpanEntry[];

export function getMessageClass(message: string): string {
  if (message === "this postcondition holds") return "postcondition";
  if (message === "the precondition always holds") return "precondition";
  if (
    message === "this loop invariant holds on entry" ||
    message === "this loop invariant is maintained by the loop"
  )
    return "loop-invariant";
  return "exact";
}

export function messagesMatch(topMessage: string, rangeMessage: string): boolean {
  const cls = getMessageClass(topMessage);
  if (cls === "postcondition") return rangeMessage === "ensures clause";
  if (cls === "precondition") return rangeMessage.startsWith("requires clause at");
  if (cls === "loop-invariant") return rangeMessage === "loop invariant always holds";
  return topMessage.trim() === rangeMessage.trim();
}

export function isContained(
  line: number,
  col: number,
  sL: number,
  sC: number,
  eL: number,
  eC: number
): boolean {
  if (line < sL || line > eL) return false;
  if (line === sL && col < sC) return false;
  if (line === eL && col > eC) return false;
  return true;
}

export function findTightestSpan(
  spanMap: SpanMap,
  file: string,
  line: number,
  col: number,
  topMessage: string
): SpanEntry | null {
  let best: SpanEntry | null = null;
  let bestLines = Infinity;
  let bestCols = Infinity;

  for (const entry of spanMap) {
    if (entry.file !== file) continue;
    if (!isContained(line, col, entry.startLine, entry.startCol, entry.endLine, entry.endCol)) continue;
    if (!messagesMatch(topMessage, entry.message)) continue;

    const lines = entry.endLine - entry.startLine;
    const cols = entry.endCol - entry.startCol;
    if (lines < bestLines || (lines === bestLines && cols < bestCols)) {
      best = entry;
      bestLines = lines;
      bestCols = cols;
    }
  }

  return best;
}

const enum BlockType {
  NoBlock = 0,
  Assertion = 1,
  ProofDep = 2,
  Unused = 3,
}

export const STRICT_SPAN_MERGE = typeof process !== "undefined" && (process.env?.NODE_ENV === "test" || process.env?.STRICT_SPAN_MERGE === "1");

export class Proof {
  proofGraph: ProofGraph;
  lineStatus: CovStatus[];

  constructor(proofLog: string, sourceCode: string) {
    this.proofGraph = new ProofGraph();
    this.lineStatus = [];

    const lines = proofLog.split(/\r?\n/);

    // Pre-pass: collect all range entries into spanMap
    const rangeRe = /^ *(.+?)\((\d+),\s*(\d+)\)-\((\d+),\s*(\d+)\):\s*(.+)$/;
    const spanMap: SpanMap = [];
    for (let i = 0; i < lines.length; i++) {
      const m = lines[i].match(rangeRe);
      if (!m) continue;
      spanMap.push({
        file: m[1].trim(),
        startLine: parseInt(m[2], 10),
        startCol: parseInt(m[3], 10),
        endLine: parseInt(m[4], 10),
        endCol: parseInt(m[5], 10),
        message: m[6].trim(),
      });
    }

    let assertionBatch: number | null = null;
    let currentTopAssertion: Node | null = null;
    let currentBlock: BlockType = BlockType.NoBlock;

    for (let i = 0; i < lines.length; i++) {
      const raw = lines[i];
      if (raw == null) continue;
      const line = raw.trim();
      if (line === "") continue;

      const batchMatch = line.match(/^\s*Assertion batch\s+(\d+)\s*:/i);
      if (batchMatch) {
        assertionBatch = parseInt(batchMatch[1], 10);
        currentBlock = BlockType.NoBlock;
        currentTopAssertion = null;
        continue;
      }
      if (assertionBatch == null) {
        continue;
      }

      if (/^Assertions:\s*$/i.test(line)) {
        currentBlock = BlockType.Assertion;
        continue;
      }
      if (/^Proof dependencies:\s*$/i.test(line)) {
        currentBlock = BlockType.ProofDep;
        continue;
      }
      if (/^Unused by proof:\s*$/i.test(line)) {
        currentBlock = BlockType.Unused;
        continue;
      }
      if (currentBlock === BlockType.NoBlock) {
        continue;
      }

      const rangeRe = /^ *(.+?)\((\d+),\s*(\d+)\)-\((\d+),\s*(\d+)\):\s*(.+)$/;
      const pointRe = /^ *(.+?)\((\d+),\s*(\d+)\):\s*(.+)$/;
      const m = line.match(rangeRe);
      const n = line.match(pointRe);

      let token: Node | null = null;
      const isTopAssertion = currentBlock === BlockType.Assertion;

      if (m) {
        const file = m[1].trim();
        const sLine = parseInt(m[2], 10);
        const sCol = parseInt(m[3], 10);
        const eLine = parseInt(m[4], 10);
        const eCol = parseInt(m[5], 10);
        const proofText = m[6].trim();
        token = new Node(file, sLine, sCol, eLine, eCol, proofText, isTopAssertion);
      } else if (n) {
        const file = n[1].trim();
        const sLine = parseInt(n[2], 10);
        const sCol = parseInt(n[3], 10);
        const proofText = n[4].trim();
        token = new Node(file, sLine, sCol, sLine, sCol, proofText, isTopAssertion);

        // Span promotion: point-only top assertions get promoted to full-range
        if (isTopAssertion) {
          const originalPointId = token.id;
          const match = findTightestSpan(spanMap, file, sLine, sCol, proofText);
          if (match) {
            const promotedNode = new Node(match.file, match.startLine, match.startCol, match.endLine, match.endCol, proofText, true);
            if (this.proofGraph.hasNode(promotedNode.id)) {
              token = this.proofGraph.getNode(promotedNode.id)!;
            } else {
              token = promotedNode;
            }

            // If the original point node already exists in the graph (added by
            // a previous iteration, e.g. as a proof dependency), transfer its
            // edges to the promoted range node and remove the orphan point.
            if (token.id !== originalPointId && this.proofGraph.hasNode(originalPointId)) {
              const oldPointNode = this.proofGraph.getNode(originalPointId)!;
              // Transfer edges: parents that oldPointNode proves
              for (const parent of oldPointNode.proves) {
                parent.provedBy.delete(oldPointNode);
                if (parent.id !== token.id) {
                  parent.provedBy.add(token);
                  token.proves.add(parent);
                }
              }
              // Transfer edges: children that prove oldPointNode
              for (const child of oldPointNode.provedBy) {
                child.proves.delete(oldPointNode);
                if (child.id !== token.id) {
                  child.proves.add(token);
                  token.provedBy.add(child);
                }
              }
              this.proofGraph.removeNode(originalPointId);
              if (this.proofGraph.hasTopNode(originalPointId)) {
                this.proofGraph.removeTopNode(originalPointId);
              }
            }
          } else if (STRICT_SPAN_MERGE) {
            throw new Error(`STRICT_SPAN_MERGE: no matching span for point ${file}(${sLine},${sCol}): ${proofText}`);
          }
        }
      } else {
        continue;
      }

      if (!this.proofGraph.hasNode(token.id)) {
        this.proofGraph.addNode(token);
      } else {
        token = this.proofGraph.getNode(token.id)!;
      }

      if (isTopAssertion) {
        // Check if an existing top node already contains this point-node's
        // start position. This handles sub-expression assertion batches that
        // Dafny emits for parts of a postcondition (e.g. just the `==` in
        // `ensures 2 == 3`). Instead of creating a duplicate orphan top, we
        // merge into the existing wider-range top node.
        let mergedIntoExisting = false;
        if (token.start.line === token.end.line && token.start.col === token.end.col) {
          // Point-node: look for an existing top that contains this point
          for (const existingTop of this.proofGraph.getAllTopNodes()) {
            if (
              existingTop.id !== token.id &&
              existingTop.start.line <= token.start.line &&
              token.start.line <= existingTop.end.line &&
              existingTop.start.col <= token.start.col &&
              token.start.col <= existingTop.end.col
            ) {
              // Existing top contains this point — merge into it
              currentTopAssertion = existingTop;
              // Remove the orphan point-node from the graph if it was just added
              if (this.proofGraph.hasNode(token.id) && token.proves.size === 0 && token.provedBy.size === 0) {
                this.proofGraph.removeNode(token.id);
              }
              mergedIntoExisting = true;
              break;
            }
          }
        }

        if (!mergedIntoExisting) {
          currentTopAssertion = token;
          currentTopAssertion.updateIsTopAssertion(isTopAssertion);

          if (!this.proofGraph.hasTopNode(token.id)) {
            this.proofGraph.addTopNode(token);
          }
        }
      } else if (currentTopAssertion != null) {
        if (currentBlock === BlockType.ProofDep || currentBlock === BlockType.Unused) {
          // Promotion: if the node's range contains the top assertion's start point,
          // the range-node replaces the phantom point-node as the top node.
          // This handles: manual assertions (same start), ensures clauses (wider range
          // starting before the postcondition point), requires clauses (same pattern).
          // Applied to both ProofDep and Unused blocks — Dafny may place the ensures
          // clause range in either section (e.g. impossible precondition → Unused).
          // Skip this promotion if the top was already promoted by span-merge (non-point).
          const topIsPoint = currentTopAssertion.start.line === currentTopAssertion.end.line &&
            currentTopAssertion.start.col === currentTopAssertion.end.col;
          if (
            topIsPoint &&
            token.id !== currentTopAssertion.id &&
            token.start.line <= currentTopAssertion.start.line &&
            currentTopAssertion.start.line <= token.end.line &&
            token.start.col <= currentTopAssertion.start.col &&
            currentTopAssertion.start.col <= token.end.col
          ) {
            token.updateIsTopAssertion(true);
            this.proofGraph.replaceTopNode(currentTopAssertion, token);
            currentTopAssertion = token;
            // Don't add an edge from the top to itself — they merged.
          } else if (currentBlock === BlockType.ProofDep) {
            this.proofGraph.addEdge(currentTopAssertion.id, token.id);
          }
          // Unused items that don't promote are just added to the graph (already done above)
          // but NOT connected as proof dependencies.
        }

        if (currentBlock === BlockType.ProofDep) {

          // "ensures clause at" postcall pattern for cross-method postcondition connections
          const postcall =
            /ensures clause at\s+([^\s()]+)\((\d+),(\d+)\)-\((\d+),(\d+)\)/;
          const pm = line.match(postcall);
          if (pm) {
            const file = pm[1].trim();
            const sLine = parseInt(pm[2], 10);
            const sCol = parseInt(pm[3], 10);
            const eLine = parseInt(pm[4], 10);
            const eCol = parseInt(pm[5], 10);

            let posttoken = new Node(
              file, sLine, sCol, eLine, eCol,
              "Post called externally", isTopAssertion,
            );
            if (!this.proofGraph.hasNode(posttoken.id)) {
              this.proofGraph.addNode(posttoken);
            } else {
              posttoken = this.proofGraph.getNode(posttoken.id)!;
            }

            // A new brnach with only one elemnt has to be created with the call
            token.isTopAssertion = true;
            if (!this.proofGraph.hasTopNode(token.id)) {
              this.proofGraph.addTopNode(token);
            }

            this.proofGraph.addEdge(token.id, posttoken.id);
          }

          // "requires clause at" precall pattern for cross-method precondition connections
          const precall =
            /requires clause at\s+([^\s()]+)\((\d+),(\d+)\)-\((\d+),(\d+)\)/;
          const prm = line.match(precall);
          if (prm) {
            const file = prm[1].trim();
            const sLine = parseInt(prm[2], 10);
            const sCol = parseInt(prm[3], 10);
            const eLine = parseInt(prm[4], 10);
            const eCol = parseInt(prm[5], 10);

            let pretoken = new Node(
              file, sLine, sCol, eLine, eCol,
              "Pre called externally", isTopAssertion,
            );
            if (!this.proofGraph.hasNode(pretoken.id)) {
              this.proofGraph.addNode(pretoken);
            } else {
              pretoken = this.proofGraph.getNode(pretoken.id)!;
            }

            // A new brnach with only one elemnt has to be created with the call
            token.isTopAssertion = true;
            if (!this.proofGraph.hasTopNode(token.id)) {
              this.proofGraph.addTopNode(token);
            }
            this.proofGraph.addEdge(token.id, pretoken.id);
          }
        }
      }
    }

    this.setCoverageStatus();
    this.setLineStatus(sourceCode);
  }

  private setLineStatus(code: string): void {
    const tokens = this.proofGraph.getAllNodes();
    const lines = code.split("\n");
    this.lineStatus = new Array(lines.length).fill(CovStatus.CovComplete);
    if (!tokens || tokens.length === 0) return;
    for (const t of tokens) {
      if (!t || !t.start || !t.end) continue;
      const sLine = Math.max(1, t.start.line || 1);
      const mapped = t.covStatus;
      const idx = sLine - 1;
      if (this.lineStatus[idx] === CovStatus.Uncovered) {
        continue;
      }
      if (mapped === CovStatus.Uncovered) {
        this.lineStatus[idx] = CovStatus.Uncovered;
      } else if (mapped === CovStatus.CovTest) {
        this.lineStatus[idx] = CovStatus.CovTest;
      }
    }
  }

  private setCoverageStatus(): void {
    const allTopTokensArray = this.proofGraph.getAllTopNodes();

    // CovStatusInternal: BFS from postcondition top nodes → CovComplete
    const allPostconditions = allTopTokensArray.filter(
      (t) => t.type === TokenType.Postcondition,
    );
    for (const post of allPostconditions) {
      post.covStatusInternal = CovStatus.CovComplete;
      const postneighbors = this.proofGraph.getBFSNeighbors(post.id, true, false);
      if (postneighbors) {
        for (const result of postneighbors) {
          result.node.covStatusInternal = CovStatus.CovComplete;
        }
      }
    }

    const allTopNotPost = allTopTokensArray.filter(
      (t) => t.type !== TokenType.Postcondition,
    );
    
    // All other top nodes are covComplete 
    // If top is assertion automatic then childs are also complete else childs are covTest
    // Call and other types are covTest
    // Exception: No children all stay Uncovered

    for (const top of allTopNotPost) {
      const neighbors = this.proofGraph.getBFSNeighbors(top.id, true, false);
      const hasChildren = neighbors != null && neighbors.length > 0;
      if (!hasChildren) {
        // If not has children is vacuously True stays uncovered
        continue
      }
      if(top.type != TokenType.AssertionManual && top.type != TokenType.LoopInvariant){
        // Assertion manual and LoopInvariant only marked as complete if any child of it is marked as complete
        top.covStatusInternal = CovStatus.CovComplete;
      }
      if (neighbors) {
        for (const result of neighbors) {
          if (result.node.covStatusInternal == CovStatus.CovComplete) {
            top.covStatusInternal = CovStatus.CovComplete;
          }
          if(top.type == TokenType.AssertionAutomatic){
               result.node.covStatusInternal = CovStatus.CovComplete
               // Dont like the aproach but it seems that is reasonalbe
               result.node.covStatus = CovStatus.CovComplete
          } 
          else if(result.node.covStatusInternal !== CovStatus.CovComplete) {
               result.node.covStatusInternal = CovStatus.CovTest;    
            }
          }
        }
      }
    

    // PER TOKEN AFTER INTERNAL IS CREATED 

    // CovStatus per token class
    const allTokensArray = this.proofGraph.getAllNodes();

    // CodeLines: equal to CovStatusInternal
    const allCodeLines = allTokensArray.filter(
      (t) => t.type === TokenType.CodeLine,
    );
    for (const token of allCodeLines) {
      token.covStatus = token.covStatusInternal;
    }

    // ManualAssertions: CovComplete only if internal is CovComplete, else Uncovered
    const allManualAssertions = allTokensArray.filter(
      (t) => t.type === TokenType.AssertionManual,
    );
    for (const token of allManualAssertions) {
      if (token.covStatusInternal === CovStatus.CovComplete) {
        token.covStatus = CovStatus.CovComplete;
      } else {
        token.covStatus = CovStatus.Uncovered;
      }
    }

    // LoopInvariants: same as ManualAssertions — CovComplete only if internal is CovComplete, else Uncovered
    const allLoopInvariants = allTokensArray.filter(
      (t) => t.type === TokenType.LoopInvariant,
    );
    for (const token of allLoopInvariants) {
      if (token.covStatusInternal === CovStatus.CovComplete) {
        token.covStatus = CovStatus.CovComplete;
      } else {
        token.covStatus = CovStatus.Uncovered;
      }
    }

    // AssertionAutomatic: Marked as always CovComplete (even though can sometimes not be)
    // Tool limitation
    const allAutomaticAssertions = allTokensArray.filter(
      (t) => t.type === TokenType.AssertionAutomatic,
    );
    for (const token of allAutomaticAssertions) {
      token.covStatus = CovStatus.CovComplete;
    }

    const allCall = allTokensArray.filter(
      (t) => t.type === TokenType.Call,
    );
    for (const token of allCall) {
      token.covStatus = token.covStatusInternal;
    }

    // Preconditions: equal to CovStatusInternal
    const allPreconditions = allTokensArray.filter(
      (t) => t.type === TokenType.Precondition,
    );
    for (const token of allPreconditions) {
      token.covStatus = token.covStatusInternal;
    }

    // Postconditions (top): alias/parent/child policy
    for (const post of allPostconditions) {
      const postneighbors = this.proofGraph.getBFSNeighbors(post.id, true, false);
      let anychildIsCovComplete = false;
      if (postneighbors) {
        for (const result of postneighbors) {
          if (
            result.node.type !== TokenType.Postcondition &&
            result.node.covStatus === CovStatus.CovComplete
          ) {
            anychildIsCovComplete = true;
            break;
          }
        }
      }

      let anyParents = false;
      const postParents = this.proofGraph.getBFSNeighbors(post.id, false);
      if (postParents && postParents.length > 0) {
        anyParents = true;
      }

      if (anyParents && anychildIsCovComplete) {
        post.covStatus = CovStatus.CovComplete;
      } else if (anychildIsCovComplete) {
        post.covStatus = CovStatus.CovTest;
      }
    }

    // Postconditions (non-top): equal to CovStatusInternal
    const allPostconditionsNonTop = allTokensArray.filter(
      (t) => t.type === TokenType.Postcondition && !t.isTopAssertion,
    );
    for (const token of allPostconditionsNonTop) {
      token.covStatus = token.covStatusInternal;
    }
  }
}

export function parseProof(dafnyCode: string, proofLog: string): Proof {
  return new Proof(proofLog, dafnyCode);
}
