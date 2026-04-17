"use strict";
(() => {
  var __defProp = Object.defineProperty;
  var __defNormalProp = (obj, key, value) => key in obj ? __defProp(obj, key, { enumerable: true, configurable: true, writable: true, value }) : obj[key] = value;
  var __publicField = (obj, key, value) => __defNormalProp(obj, typeof key !== "symbol" ? key + "" : key, value);

  // packages/core/src/types.ts
  var CovStatus = /* @__PURE__ */ ((CovStatus2) => {
    CovStatus2["CovComplete"] = "CovComplete";
    CovStatus2["CovTest"] = "CovTest";
    CovStatus2["Uncovered"] = "Uncovered";
    return CovStatus2;
  })(CovStatus || {});
  var TokenType = /* @__PURE__ */ ((TokenType2) => {
    TokenType2["Undefined"] = "Undefined";
    TokenType2["Precondition"] = "Precondition";
    TokenType2["Postcondition"] = "Postcondition";
    TokenType2["AssertionManual"] = "AssertionManual";
    TokenType2["AssertionAutomatic"] = "AssertionAutomatic";
    TokenType2["CodeLine"] = "CodeLine";
    return TokenType2;
  })(TokenType || {});

  // packages/core/src/node.ts
  var Node = class _Node {
    constructor(file, sLine, sCol, eLine, eCol, prooftext, isTopAssertion) {
      __publicField(this, "id");
      __publicField(this, "file");
      __publicField(this, "start");
      __publicField(this, "end");
      __publicField(this, "prooftext");
      __publicField(this, "isTopAssertion");
      __publicField(this, "topAliasNode");
      __publicField(this, "covStatus");
      __publicField(this, "covStatusInternal");
      __publicField(this, "type");
      __publicField(this, "proves");
      __publicField(this, "provedBy");
      this.file = file;
      this.prooftext = prooftext;
      this.start = { line: sLine, col: sCol };
      this.end = { line: eLine, col: eCol };
      this.isTopAssertion = isTopAssertion;
      this.topAliasNode = null;
      this.covStatus = "Uncovered" /* Uncovered */;
      this.covStatusInternal = "Uncovered" /* Uncovered */;
      this.type = "Undefined" /* Undefined */;
      this.id = `${this.file}:${this.start.line},${this.start.col}-${this.end.line},${this.end.col}`;
      this.proves = /* @__PURE__ */ new Set();
      this.provedBy = /* @__PURE__ */ new Set();
      this.updateIsTopAssertion(isTopAssertion);
    }
    updateIsTopAssertion(isTopAssertion) {
      this.isTopAssertion = isTopAssertion;
      if (this.prooftext.includes("this postcondition holds")) {
        this.type = "Postcondition" /* Postcondition */;
      } else if (this.prooftext.includes("ensures clause")) {
        this.type = "Postcondition" /* Postcondition */;
      } else if (this.prooftext.includes("method requires clause")) {
        this.type = "Precondition" /* Precondition */;
      } else if (this.prooftext.includes("assertion always holds")) {
        this.type = "AssertionManual" /* AssertionManual */;
      } else if (this.prooftext.includes("index in range") || this.prooftext.includes("target object is never null") || this.prooftext.includes(
        "which is subject to definite-assignment rules, is always initialized at this return point"
      ) || this.prooftext.includes(
        "which is subject to definite-assignment rules, is always initialized here"
      )) {
        this.type = "AssertionAutomatic" /* AssertionAutomatic */;
      } else if (this.isTopAssertion) {
        this.type = "AssertionAutomatic" /* AssertionAutomatic */;
      } else {
        this.type = "CodeLine" /* CodeLine */;
      }
    }
    connectTo(target) {
      this.provedBy.add(target);
      target.proves.add(this);
    }
    toJSON() {
      return {
        id: this.id,
        file: this.file,
        start: { ...this.start },
        end: { ...this.end },
        prooftext: this.prooftext,
        isTopAssertion: this.isTopAssertion,
        type: this.type,
        covStatus: this.covStatus,
        covStatusInternal: this.covStatusInternal
      };
    }
    static fromJSON(data) {
      const node = new _Node(
        data.file,
        data.start.line,
        data.start.col,
        data.end.line,
        data.end.col,
        data.prooftext,
        data.isTopAssertion
      );
      node.type = data.type;
      node.covStatus = data.covStatus;
      node.covStatusInternal = data.covStatusInternal;
      return node;
    }
  };

  // packages/core/src/proof-graph.ts
  var ProofGraph = class _ProofGraph {
    constructor() {
      __publicField(this, "nodes");
      __publicField(this, "topNodes");
      this.nodes = /* @__PURE__ */ new Map();
      this.topNodes = /* @__PURE__ */ new Map();
    }
    addNode(node) {
      this.nodes.set(node.id, node);
    }
    getNode(id) {
      return this.nodes.get(id);
    }
    hasNode(id) {
      return this.nodes.has(id);
    }
    addTopNode(node) {
      this.topNodes.set(node.id, node);
    }
    getTopNode(id) {
      return this.topNodes.get(id);
    }
    hasTopNode(id) {
      return this.topNodes.has(id);
    }
    addEdge(fromId, toId) {
      const from = this.getNode(fromId);
      const to = this.getNode(toId);
      if (!from || !to) {
        throw new Error(`Invalid edge: ${fromId} -> ${toId}`);
      }
      from.connectTo(to);
    }
    getAllNodes() {
      return Array.from(this.nodes.values());
    }
    getAllTopNodes() {
      return Array.from(this.topNodes.values());
    }
    getBFSNeighbors(key, isProvedBy, getAll = false) {
      if (!this.hasNode(key)) {
        return null;
      }
      const token = this.getNode(key);
      const neighbors = /* @__PURE__ */ new Set();
      const queue = [{ node: token }];
      const visited = /* @__PURE__ */ new Set([token.id]);
      while (queue.length > 0) {
        const { node } = queue.shift();
        let targetSet;
        if (getAll) {
          targetSet = /* @__PURE__ */ new Set([...node.provedBy, ...node.proves]);
        } else {
          targetSet = isProvedBy ? node.provedBy : node.proves;
        }
        for (const pred of targetSet) {
          if (visited.has(pred.id)) {
            continue;
          }
          visited.add(pred.id);
          neighbors.add(pred);
          queue.push({ node: pred });
        }
      }
      return [...neighbors];
    }
    toJSON() {
      const nodes = this.getAllNodes().map((n) => n.toJSON());
      const topNodeIds = this.getAllTopNodes().map((n) => n.id);
      const edges = [];
      for (const node of this.getAllNodes()) {
        for (const child of node.provedBy) {
          edges.push({ from: node.id, to: child.id });
        }
      }
      return { nodes, topNodeIds, edges };
    }
    static fromJSON(data) {
      const graph = new _ProofGraph();
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
  };

  // packages/core/src/proof.ts
  var Proof = class {
    constructor(proofLog, sourceCode) {
      __publicField(this, "proofGraph");
      __publicField(this, "lineStatus");
      this.proofGraph = new ProofGraph();
      this.lineStatus = [];
      const lines = proofLog.split(/\r?\n/);
      let assertionBatch = null;
      let currentTopAssertion = null;
      let currentBlock = 0 /* NoBlock */;
      for (let i = 0; i < lines.length; i++) {
        const raw = lines[i];
        if (raw == null) continue;
        const line = raw.trim();
        if (line === "") continue;
        const batchMatch = line.match(/^\s*Assertion batch\s+(\d+)\s*:/i);
        if (batchMatch) {
          assertionBatch = parseInt(batchMatch[1], 10);
          currentBlock = 0 /* NoBlock */;
          currentTopAssertion = null;
          continue;
        }
        if (assertionBatch == null) {
          continue;
        }
        if (/^Assertions:\s*$/i.test(line)) {
          currentBlock = 1 /* Assertion */;
          continue;
        }
        if (/^Proof dependencies:\s*$/i.test(line)) {
          currentBlock = 2 /* ProofDep */;
          continue;
        }
        if (/^Unused by proof:\s*$/i.test(line)) {
          currentBlock = 3 /* Unused */;
          continue;
        }
        if (currentBlock === 0 /* NoBlock */) {
          continue;
        }
        const rangeRe = /^ *(.+?)\((\d+),\s*(\d+)\)-\((\d+),\s*(\d+)\):\s*(.+)$/;
        const pointRe = /^ *(.+?)\((\d+),\s*(\d+)\):\s*(.+)$/;
        const m = line.match(rangeRe);
        const n = line.match(pointRe);
        let token = null;
        const isTopAssertion = currentBlock === 1 /* Assertion */;
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
          token = this.proofGraph.getNode(token.id);
        }
        if (isTopAssertion) {
          currentTopAssertion = token;
          currentTopAssertion.updateIsTopAssertion(isTopAssertion);
          if (!this.proofGraph.hasTopNode(token.id)) {
            this.proofGraph.addTopNode(token);
          }
        } else if (currentTopAssertion != null) {
          if (currentBlock === 2 /* ProofDep */) {
            if (token.start.line <= currentTopAssertion.start.line && currentTopAssertion.start.line <= token.end.line && token.start.col <= currentTopAssertion.start.col && currentTopAssertion.start.col <= token.end.col) {
              if (!currentTopAssertion.topAliasNode) {
                currentTopAssertion.topAliasNode = token;
              } else {
                const rangePoss = token.end.col - token.start.col;
                const rangeActual = currentTopAssertion.topAliasNode.end.col - currentTopAssertion.topAliasNode.start.col;
                if (rangePoss > rangeActual) {
                  currentTopAssertion.topAliasNode = token;
                }
              }
            }
            this.proofGraph.addEdge(currentTopAssertion.id, token.id);
            const postcall = /ensures clause at\s+([^\s()]+)\((\d+),(\d+)\)-\((\d+),(\d+)\)/;
            const pm = line.match(postcall);
            if (pm) {
              const file = pm[1].trim();
              const sLine = parseInt(pm[2], 10);
              const sCol = parseInt(pm[3], 10);
              const eLine = parseInt(pm[4], 10);
              const eCol = parseInt(pm[5], 10);
              let posttoken = new Node(
                file,
                sLine,
                sCol,
                eLine,
                eCol,
                "Post called externally",
                isTopAssertion
              );
              if (!this.proofGraph.hasNode(posttoken.id)) {
                this.proofGraph.addNode(posttoken);
              } else {
                posttoken = this.proofGraph.getNode(posttoken.id);
              }
              this.proofGraph.addEdge(token.id, posttoken.id);
            }
          }
        }
      }
      this.setCoverageStatus();
      this.setLineStatus(sourceCode);
    }
    setLineStatus(code) {
      const tokens = this.proofGraph.getAllNodes();
      const lines = code.split("\n");
      this.lineStatus = new Array(lines.length).fill("CovComplete" /* CovComplete */);
      if (!tokens || tokens.length === 0) return;
      for (const t of tokens) {
        if (!t || !t.start || !t.end) continue;
        const sLine = Math.max(1, t.start.line || 1);
        const mapped = t.covStatus;
        const idx = sLine - 1;
        if (this.lineStatus[idx] === "Uncovered" /* Uncovered */) {
          continue;
        }
        if (mapped === "Uncovered" /* Uncovered */) {
          this.lineStatus[idx] = "Uncovered" /* Uncovered */;
        } else if (mapped === "CovTest" /* CovTest */) {
          this.lineStatus[idx] = "CovTest" /* CovTest */;
        }
      }
    }
    setCoverageStatus() {
      const allTopTokensArray = this.proofGraph.getAllTopNodes();
      const allPostconditions = allTopTokensArray.filter(
        (t) => t.type === "Postcondition" /* Postcondition */
      );
      for (const post of allPostconditions) {
        post.covStatusInternal = "CovComplete" /* CovComplete */;
        const postneighbors = this.proofGraph.getBFSNeighbors(post.id, true, true);
        if (postneighbors) {
          for (const neigh of postneighbors) {
            neigh.covStatusInternal = "CovComplete" /* CovComplete */;
          }
        }
      }
      const allTopNotPost = allTopTokensArray.filter(
        (t) => t.type !== "Postcondition" /* Postcondition */
      );
      for (const top of allTopNotPost) {
        top.covStatusInternal = "CovComplete" /* CovComplete */;
        const neighbors = this.proofGraph.getBFSNeighbors(top.id, true, true);
        if (neighbors) {
          for (const neigh of neighbors) {
            if (neigh.covStatusInternal !== "CovComplete" /* CovComplete */) {
              neigh.covStatusInternal = "CovTest" /* CovTest */;
            }
          }
        }
      }
      const allTokensArray = this.proofGraph.getAllNodes();
      const allCodeLines = allTokensArray.filter(
        (t) => t.type === "CodeLine" /* CodeLine */
      );
      for (const token of allCodeLines) {
        token.covStatus = token.covStatusInternal;
      }
      const allAutoAssertions = allTokensArray.filter(
        (t) => t.type === "AssertionAutomatic" /* AssertionAutomatic */
      );
      for (const token of allAutoAssertions) {
        token.covStatus = "CovComplete" /* CovComplete */;
      }
      const allManualAssertions = allTokensArray.filter(
        (t) => t.type === "AssertionManual" /* AssertionManual */
      );
      for (const token of allManualAssertions) {
        if (token.covStatusInternal === "CovComplete" /* CovComplete */) {
          token.covStatus = "CovComplete" /* CovComplete */;
        } else {
          token.covStatus = "Uncovered" /* Uncovered */;
        }
      }
      const allPreconditions = allTokensArray.filter(
        (t) => t.type === "Precondition" /* Precondition */
      );
      for (const token of allPreconditions) {
        token.covStatus = token.covStatusInternal;
      }
      for (const post of allPostconditions) {
        const postneighbors = this.proofGraph.getBFSNeighbors(post.id, true, true);
        let anychildIsCovComplete = false;
        if (postneighbors) {
          for (const neigh of postneighbors) {
            if (neigh.type !== "Postcondition" /* Postcondition */ && neigh.covStatus === "CovComplete" /* CovComplete */) {
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
          post.covStatus = "CovComplete" /* CovComplete */;
        } else if (anychildIsCovComplete) {
          post.covStatus = "CovTest" /* CovTest */;
        } else {
          post.covStatus = "Uncovered" /* Uncovered */;
        }
      }
      const allPostconditionsNonTop = allTokensArray.filter(
        (t) => t.type === "Postcondition" /* Postcondition */ && !t.isTopAssertion
      );
      for (const token of allPostconditionsNonTop) {
        token.covStatus = token.covStatusInternal;
      }
    }
  };
  function parseProof(dafnyCode, proofLog) {
    return new Proof(proofLog, dafnyCode);
  }

  // packages/core/src/rendering.ts
  function escapeHtml(str) {
    return String(str).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;").replace(/'/g, "&#39;");
  }
  function tokenAttrs(tok) {
    let statusStr = "";
    if (tok && tok.covStatus) {
      if (tok.covStatus === "Uncovered" /* Uncovered */) statusStr = "uncovered";
      else if (tok.covStatus === "CovTest" /* CovTest */) statusStr = "covered-test";
      else statusStr = "covered-complete";
    }
    const dataId = escapeHtml(tok.id);
    const dataStatus = escapeHtml(statusStr);
    const classes = escapeHtml("token");
    const istopAttr = tok.isTopAssertion ? ' data-istop="true"' : "";
    return { dataId, dataStatus, classes, istopAttr };
  }
  function generateSpansFragment(code, graph) {
    const lines = code.split("\n");
    const lineStart = new Array(lines.length + 2);
    let pos = 0;
    for (let i = 0; i < lines.length; ++i) {
      lineStart[i + 1] = pos;
      pos += lines[i].length + 1;
    }
    const ranges = [];
    const tokensArray = graph.getAllNodes();
    for (const t of tokensArray) {
      if (!t || !t.start || !t.end) continue;
      const sLine = t.start.line, sCol = t.start.col, eLine = t.end.line, eCol = t.end.col;
      if (!Number.isInteger(sLine) || !Number.isInteger(sCol) || !Number.isInteger(eLine) || !Number.isInteger(eCol)) continue;
      if (sLine < 1 || sLine > lines.length || eLine < 1 || eLine > lines.length) continue;
      const startIndex = lineStart[sLine] + Math.max(0, sCol - 1);
      const endIndex = lineStart[eLine] + eCol;
      if (isNaN(startIndex) || isNaN(endIndex) || startIndex < 0 || endIndex < startIndex) continue;
      ranges.push({ startIndex, endIndex, token: t, children: [] });
    }
    ranges.sort((a, b) => a.startIndex - b.startIndex || b.endIndex - a.endIndex);
    const roots = [];
    const stack = [];
    for (const r of ranges) {
      while (stack.length && r.startIndex >= stack[stack.length - 1].endIndex) stack.pop();
      if (stack.length === 0) {
        roots.push(r);
        stack.push(r);
      } else {
        const parent = stack[stack.length - 1];
        if (r.endIndex <= parent.endIndex) {
          parent.children.push(r);
          stack.push(r);
        }
      }
    }
    function renderNode(node) {
      const { dataId, dataStatus, classes, istopAttr } = tokenAttrs(node.token);
      let innerOut = "";
      let cursor2 = node.startIndex;
      if (node.children.length) {
        node.children.sort((a, b) => a.startIndex - b.startIndex);
        for (const child of node.children) {
          if (cursor2 < child.startIndex) innerOut += escapeHtml(code.slice(cursor2, child.startIndex));
          innerOut += renderNode(child);
          cursor2 = child.endIndex;
        }
      }
      if (cursor2 < node.endIndex) innerOut += escapeHtml(code.slice(cursor2, node.endIndex));
      return `<span class="${classes}" data-id="${dataId}" ${istopAttr} data-status="${dataStatus}">${innerOut}</span>`;
    }
    let out = "";
    let cursor = 0;
    roots.sort((a, b) => a.startIndex - b.startIndex);
    for (const rootNode of roots) {
      if (cursor < rootNode.startIndex) out += escapeHtml(code.slice(cursor, rootNode.startIndex));
      out += renderNode(rootNode);
      cursor = rootNode.endIndex;
    }
    if (cursor < code.length) out += escapeHtml(code.slice(cursor));
    return out;
  }
  function getDependsOn(key, graph) {
    if (!graph.hasNode(key)) return null;
    return graph.getBFSNeighbors(key, false, true);
  }

  // packages/core/src/browser-entry.ts
  var root = typeof window !== "undefined" ? window : typeof global !== "undefined" ? global : {};
  root.CovStatus = CovStatus;
  root.TokenType = TokenType;
  root.sampleLog = "";
  root.sourceCode = "";
  root.targetFileName = "_USECASE_find_irrelevant_lines_for_proof.dfy";
  root.parseProof = function(dafnyCode, proofLog) {
    root.sampleLog = proofLog;
    root.sourceCode = dafnyCode;
    return parseProof(dafnyCode, proofLog);
  };
  root.generateSpansFragment = function(code, proof) {
    return generateSpansFragment(code, proof.proofGraph);
  };
  root.getDependsOn = function(key, proof) {
    return getDependsOn(key, proof.proofGraph);
  };
  root.getSampleLog = function() {
    return root.sampleLog;
  };
  root.getSourceCode = function() {
    return root.sourceCode;
  };
})();
