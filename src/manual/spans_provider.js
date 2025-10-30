// spans_provider.js (environment-agnostic)
// Works in browser (as <script>) and in Node (require).

// root: window in browser, global in Node, fallback to a plain object
const root = (typeof window !== 'undefined') ? window
           : (typeof global !== 'undefined') ? global
           : {};

// --- Begin original code but using `root` instead of `window` for attachment ---

root.sampleLog = `Dafny program verifier finished with 2 verified, 0 errors

Results for Abs (correctness)
  Overall outcome: Correct
  Overall time: 00:00:00.2727431
  Overall resource count: 11686
  Maximum assertion batch time: 00:00:00.1363772
  Maximum assertion batch resource count: 5868

  Assertion batch 1:
    Outcome: Valid
    Duration: 00:00:00.1363659
    Resource count: 5818

    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,21): this postcondition holds

    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20)-(2,23): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(12,5)-(12,15): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(16,1)-(18,1): function definition for Id

    Unused by proof:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19)-(3,24): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(6,5)-(6,11): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(10,5)-(10,12): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(14,1)-(14,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point

  Assertion batch 2:
    Outcome: Valid
    Duration: 00:00:00.1363772
    Resource count: 5868

    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,22): this postcondition holds

    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19)-(3,24): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(10,5)-(10,12): assignment (or return)

    Unused by proof:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20)-(2,23): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(6,5)-(6,11): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(12,5)-(12,15): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(14,1)-(14,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
`;

root.sourceCode = `method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if(x == 0){
    y := 0; // Unused by proof  _USECASE_find_irrelevant_lines.dfy(6,5)-(6,11): assignment (or return)
  }

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}
`;

root.targetFileName = '_USECASE_find_irrelevant_lines_for_proof.dfy';

root.CovStatus = {
  CovComplete: "CovComplete",
  CovTest: "CovTest",
  Uncovered: "Uncover"
};

root.TokenType = {
  Other: 0,
  Precondition: 1,
  Postcondition: 2,
  Assertion: 3,
  CodeLine: 4
};

root.prooftoken = class {
  constructor(file, sLine, sCol, eLine, eCol, prooftext, isTopAssertion) {
    this.file = file;
    this.prooftext = prooftext;
    this.start = { line: sLine, col: sCol };
    this.end = { line: eLine, col: eCol };
    this.isTopAssertion = !!isTopAssertion;

    this.CovStatus = root.CovStatus.Uncovered;
    this.tokenType = root.TokenType.Other;

    this._key = `${this.file}:${this.start.line},${this.start.col}-${this.end.line},${this.end.col}`;

    if (this.isTopAssertion) {
      this.proofUsedTokens = [];
      this.proofUnusedTokens = [];
      if (this.prooftext && this.prooftext.toLowerCase().includes('postcondition')) {
        this.tokenType = root.TokenType.Postcondition;
      } else {
        this.tokenType = root.TokenType.Assertion;
      }
    }
  }

  spanString() {
    return `(${this.start.line},${this.start.col})-(${this.end.line},${this.end.col})`;
  }
};

root.proof = class {
  constructor(proofLog) {
    const BlockType = { NoBlock: 0, Assertion: 1, ProofDep: 2, Unused: 3 };

    const lines = proofLog.split(/\r?\n/);
    let assertionBatch = null;
    let currentTopAssertion = null;
    let currentBlock = BlockType.NoBlock;

    this.allTokens = [];
    this.topLevelProofInfo = [];

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

      const sec = line;
      if (/^Assertions:\s*$/i.test(sec)) {
        currentBlock = BlockType.Assertion;
        continue;
      }
      if (/^Proof dependencies:\s*$/i.test(sec)) {
        currentBlock = BlockType.ProofDep;
        continue;
      }
      if (/^Unused by proof:\s*$/i.test(sec)) {
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

      let token = null;
      const isTopAssertion = (currentBlock === BlockType.Assertion);

      if (m) {
        const file = m[1].trim();
        const sLine = parseInt(m[2], 10);
        const sCol = parseInt(m[3], 10);
        const eLine = parseInt(m[4], 10);
        const eCol = parseInt(m[5], 10);
        const proofText = m[6].trim();

        token = new root.prooftoken(file, sLine, sCol, eLine, eCol, proofText, isTopAssertion);
      } else if (n) {
        const file = n[1].trim();
        const sLine = parseInt(n[2], 10);
        const sCol = parseInt(n[3], 10);
        const proofText = n[4].trim();

        token = new root.prooftoken(file, sLine, sCol, sLine, sCol + 1, proofText, isTopAssertion);
      } else {
        continue;
      }

      if (!this.allTokens.some(t => t._key === token._key)) {
        this.allTokens.push(token);
      } else {
        token = this.allTokens.find(t => t._key === token._key);
      }

      if (isTopAssertion) {
        currentTopAssertion = token;
        if (!this.topLevelProofInfo.some(t => t._key === token._key)) {
          this.topLevelProofInfo.push(token);
        }
      } else if (currentTopAssertion != null) {
        if (currentBlock === BlockType.ProofDep) {
          token.CovStatus = root.CovStatus.CovComplete;
          if (!currentTopAssertion.proofUsedTokens.some(t => t._key === token._key)) {
            currentTopAssertion.proofUsedTokens.push(token);
          }
        } else if (currentBlock === BlockType.Unused) {
          if (!currentTopAssertion.proofUnusedTokens.some(t => t._key === token._key)) {
            currentTopAssertion.proofUnusedTokens.push(token);
          }
        }
      }
    }
  }

  getFile(fname) {
    const elems = new Map();
    for (const t of this.allTokens) {
      if (t.file === fname) {
        elems.set(t._key, t);
      }
    }
    const tops = this.topLevelProofInfo.filter(t => t.file === fname);
    return {
      elements: elems,
      topLevelProofInfo: tops,
      getElementAt: (line, col) => {
        for (const tok of elems.values()) {
          const s = tok.start, e = tok.end;
          const beforeStart = (line < s.line) || (line === s.line && col < s.col);
          const afterEnd = (line > e.line) || (line === e.line && col > e.col);
          if (!beforeStart && !afterEnd) return tok;
        }
        return null;
      }
    };
  }
};

root.parseProof = function (log) {
  return new root.proof(log);
};

root.getTokensForFile = function (proofOrLog, fname) {
  let p = null;
  if (!proofOrLog) {
    p = new root.proof(root.sampleLog);
  } else if (typeof proofOrLog === 'string') {
    p = new root.proof(proofOrLog);
  } else if (typeof proofOrLog === 'object' && typeof proofOrLog.allTokens !== 'undefined') {
    p = proofOrLog;
  } else {
    p = new root.proof(root.sampleLog);
  }
  return p.allTokens.filter(t => t.file === fname);
};

function internalEscapeHtml(str) {
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

root.generateSpansFragment = function (code, tokens, opts = {}) {
  const skipOverlapping = opts.skipOverlapping !== false;
  const wrapTag = opts.wrapTag || 'span';
  const className = opts.className || 'token';
  const lines = code.split('\n');
  const lineStart = new Array(lines.length + 2);
  let pos = 0;
  for (let i = 0; i < lines.length; ++i) {
    lineStart[i + 1] = pos;
    pos += lines[i].length + 1;
  }

  const ranges = [];
  for (const t of tokens || []) {
    if (!t) continue;
    if (t.isTopAssertion) continue;
    if (!t.start || !t.end) continue;
    const sLine = t.start.line, sCol = t.start.col, eLine = t.end.line, eCol = t.end.col;
    if (!Number.isInteger(sLine) || !Number.isInteger(sCol) || !Number.isInteger(eLine) || !Number.isInteger(eCol)) continue;
    if (sLine < 1 || sLine > lines.length || eLine < 1 || eLine > lines.length) continue;
    const startIndex = lineStart[sLine] + Math.max(0, sCol - 1);
    const endIndex = lineStart[eLine] + eCol;
    if (isNaN(startIndex) || isNaN(endIndex) || startIndex < 0 || endIndex < startIndex) continue;
    ranges.push({ startIndex, endIndex, token: t });
  }

  ranges.sort((a, b) => b.startIndex - a.startIndex);

  const acceptedDesc = [];
  if (skipOverlapping) {
    const occupied = [];
    for (const r of ranges) {
      const overlaps = occupied.some(o => !(r.endIndex <= o[0] || r.startIndex >= o[1]));
      if (!overlaps) { acceptedDesc.push(r); occupied.push([r.startIndex, r.endIndex]); }
    }
  } else {
    acceptedDesc.push(...ranges);
  }

  const accepted = acceptedDesc.sort((a, b) => a.startIndex - b.startIndex);

  let out = '';
  let cursor = 0;
  for (const r of accepted) {
    if (cursor < r.startIndex) out += internalEscapeHtml(code.slice(cursor, r.startIndex));
    const inner = code.slice(r.startIndex, r.endIndex);
    const tok = r.token;
    let statusStr = '';
    if (tok && tok.CovStatus) {
      if (tok.CovStatus === root.CovStatus.Uncovered || String(tok.CovStatus).toLowerCase().includes('uncover')) statusStr = 'uncovered';
      else if (tok.CovStatus === root.CovStatus.CovTest || String(tok.CovStatus).toLowerCase().includes('test')) statusStr = 'covered-test';
      else statusStr = 'covered-complete';
    }
    const dataId = internalEscapeHtml(String(tok._key || `${tok.file}:${tok.start.line},${tok.start.col}`));
    const dataStatus = internalEscapeHtml(statusStr);
    const classes = internalEscapeHtml(className);
    const wrapped = `<${wrapTag} class="${classes}" data-id="${dataId}" data-status="${dataStatus}">${internalEscapeHtml(inner)}</${wrapTag}>`;
    out += wrapped;
    cursor = r.endIndex;
  }
  if (cursor < code.length) out += internalEscapeHtml(code.slice(cursor));
  return out;
};

root.getDependsOn = function (key, proof) {
  if (!proof.allTokens.some(t => t._key === key)) {
    return null;
  }

  let dependsOn = [];
  for (const topLevel of proof.topLevelProofInfo) {
    dependsOnPossibleList = [];
    for (const dependency of topLevel.proofUsedTokens) {
      if (key === dependency._key) {
        dependsOn = dependsOn.concat(dependsOnPossibleList);
        dependsOnPossibleList = [];
        break;
      }
      dependsOnPossibleList.push(dependency._key);
    }
  }

  return dependsOn; // Element not present
};

root.getUsedOn = function (key, proof) {
  if (!proof.allTokens.some(t => t._key === key)) {
    return null;
  }

  let alreadyOnDependencies = false;
  let usedOn = [];

  for (const topLevel of proof.topLevelProofInfo) {
    alreadyOnDependencies = false;
    for (const dependency of topLevel.proofUsedTokens) {
      if (key === dependency._key) {
        alreadyOnDependencies = true;
        continue;
      }
      if (alreadyOnDependencies) {
        usedOn.push(dependency._key);
      }
    }
  }

  return usedOn; // Element not present
};

// --- End original code ---

// If running under Node (CommonJS), export named symbols for unit tests
if (typeof module !== 'undefined' && typeof module.exports !== 'undefined') {
  module.exports = {
    sampleLog: root.sampleLog,
    sourceCode: root.sourceCode,
    targetFileName: root.targetFileName,
    CovStatus: root.CovStatus,
    TokenType: root.TokenType,
    prooftoken: root.prooftoken,
    proof: root.proof,
    parseProof: root.parseProof,
    getTokensForFile: root.getTokensForFile,
    generateSpansFragment: root.generateSpansFragment,
    getDependsOn: root.getDependsOn,
    getUsedOn: root.getUsedOn,
  };
}

if (require.main === module) {
   proof = root.parseProof(root.sampleLog); 
   let a = root.getUsedOn("_USECASE_find_irrelevant_lines_for_proof.dfy:10,5-10,12", proof); 
   let c = root.getDependsOn("_USECASE_find_irrelevant_lines_for_proof.dfy:10,5-10,12", proof); 
   let b = 3; 
}