import { CovStatus, TokenType } from "./types.js";
import { Node } from "./node.js";
import { ProofGraph } from "./proof-graph.js";

const enum BlockType {
  NoBlock = 0,
  Assertion = 1,
  ProofDep = 2,
  Unused = 3,
}

export class Proof {
  proofGraph: ProofGraph;
  lineStatus: CovStatus[];

  constructor(proofLog: string, sourceCode: string) {
    this.proofGraph = new ProofGraph();
    this.lineStatus = [];

    const lines = proofLog.split(/\r?\n/);

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
      } else {
        continue;
      }

      if (!this.proofGraph.hasNode(token.id)) {
        this.proofGraph.addNode(token);
      } else {
        token = this.proofGraph.getNode(token.id)!;
      }

      if (isTopAssertion) {
        currentTopAssertion = token;
        currentTopAssertion.updateIsTopAssertion(isTopAssertion);

        if (!this.proofGraph.hasTopNode(token.id)) {
          this.proofGraph.addTopNode(token);
        }
      } else if (currentTopAssertion != null) {
        if (currentBlock === BlockType.ProofDep) {
          // Alias detection: if token range contains the top assertion point
          if (
            token.start.line <= currentTopAssertion.start.line &&
            currentTopAssertion.start.line <= token.end.line &&
            token.start.col <= currentTopAssertion.start.col &&
            currentTopAssertion.start.col <= token.end.col
          ) {
            if (!currentTopAssertion.topAliasNode) {
              currentTopAssertion.topAliasNode = token;
            } else {
              const rangePoss = token.end.col - token.start.col;
              const rangeActual =
                currentTopAssertion.topAliasNode.end.col -
                currentTopAssertion.topAliasNode.start.col;
              if (rangePoss > rangeActual) {
                currentTopAssertion.topAliasNode = token;
              }
            }
          }

          this.proofGraph.addEdge(currentTopAssertion.id, token.id);

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
            this.proofGraph.addEdge(token.id, posttoken.id);
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
      const postneighbors = this.proofGraph.getBFSNeighbors(post.id, true, true);
      if (postneighbors) {
        for (const result of postneighbors) {
          result.node.covStatusInternal = CovStatus.CovComplete;
        }
      }
    }

    // CovStatusInternal: BFS from non-postcondition top nodes → CovTest (if not already CovComplete)
    const allTopNotPost = allTopTokensArray.filter(
      (t) => t.type !== TokenType.Postcondition,
    );
    for (const top of allTopNotPost) {
      top.covStatusInternal = CovStatus.CovComplete;
      const neighbors = this.proofGraph.getBFSNeighbors(top.id, true, true);
      if (neighbors) {
        for (const result of neighbors) {
          if (result.node.covStatusInternal !== CovStatus.CovComplete) {
            result.node.covStatusInternal = CovStatus.CovTest;
          }
        }
      }
    }

    // CovStatus per token class
    const allTokensArray = this.proofGraph.getAllNodes();

    // CodeLines: equal to CovStatusInternal
    const allCodeLines = allTokensArray.filter(
      (t) => t.type === TokenType.CodeLine,
    );
    for (const token of allCodeLines) {
      token.covStatus = token.covStatusInternal;
    }

    // AutoAssertions: always CovComplete
    const allAutoAssertions = allTokensArray.filter(
      (t) => t.type === TokenType.AssertionAutomatic,
    );
    for (const token of allAutoAssertions) {
      token.covStatus = CovStatus.CovComplete;
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

    // Preconditions: equal to CovStatusInternal
    const allPreconditions = allTokensArray.filter(
      (t) => t.type === TokenType.Precondition,
    );
    for (const token of allPreconditions) {
      token.covStatus = token.covStatusInternal;
    }

    // Postconditions (top): alias/parent/child policy
    for (const post of allPostconditions) {
      const postneighbors = this.proofGraph.getBFSNeighbors(post.id, true, true);
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
      const alias = post.topAliasNode;
      if (alias) {
        const postParents = this.proofGraph.getBFSNeighbors(alias.id, false);
        if (postParents && postParents.length > 1) {
          anyParents = true;
        }
      }

      if (anyParents && anychildIsCovComplete) {
        post.covStatus = CovStatus.CovComplete;
      } else if (anychildIsCovComplete) {
        post.covStatus = CovStatus.CovTest;
      } else {
        post.covStatus = CovStatus.Uncovered;
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
