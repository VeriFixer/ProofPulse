// spans_provider.js
// ES module wrapper around your proof parser + span generator
export const sampleLog = `Dafny program verifier finished with 2 verified, 0 errors

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

export const sourceCode = `method Abs(x: int) returns (y: int)
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

export const targetFileName = '_USECASE_find_irrelevant_lines_for_proof.dfy';

export const CovStatus = {
  CovComplete: "covered-complete",
  CovTest: "covered-test",
  Uncovered: "uncovered"
};

export const TokenType = {
  Other: 0,
  Precondition: 1,
  Postcondition: 2,
  Assertion: 3,
  CodeLine: 4
};

export class prooftoken {
  constructor(file, sLine, sCol, eLine, eCol, prooftext, isTopAssertion) {
    this.file = file;
    this.prooftext = prooftext;
    this.start = { line: sLine, col: sCol };
    this.end = { line: eLine, col: eCol };
    this.isTopAssertion = !!isTopAssertion;

    this.CovStatus = CovStatus.Uncovered;
    this.tokenType = TokenType.Other;

    this._key = `${this.file}:${this.start.line},${this.start.col}-${this.end.line},${this.end.col}`;

    if (this.isTopAssertion) {
      this.proofUsedTokens = [];
      this.proofUnusedTokens = [];
      if (this.prooftext && this.prooftext.toLowerCase().includes('postcondition')) {
        this.tokenType = TokenType.Postcondition;
      } else {
        this.tokenType = TokenType.Assertion;
      }
    }
  }

  spanString() {
    return `(${this.start.line},${this.start.col})-(${this.end.line},${this.end.col})`;
  }
}

export class proof {
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

        token = new prooftoken(file, sLine, sCol, eLine, eCol, proofText, isTopAssertion);
      } else if (n) {
        const file = n[1].trim();
        const sLine = parseInt(n[2], 10);
        const sCol = parseInt(n[3], 10);
        const proofText = n[4].trim();

        token = new prooftoken(file, sLine, sCol, sLine, sCol + 1, proofText, isTopAssertion);
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
          token.CovStatus = CovStatus.CovComplete;
          if (!currentTopAssertion.proofUsedTokens.some(t => t._key === token._key)) {
            currentTopAssertion.proofUsedTokens.push(token);
          }
        } else if (currentBlock === BlockType.Unused) {
          if (!currentTopAssertion.proofUnusedTokens.some(t => t._key === token._key)) {
            currentTopAssertion.proofUnusedTokens.push(token);
          }
        }
      }
    } // end for lines
  } // end constructor

  // Provide a per-file view with elements as a Map and topLevelProofInfo subset
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
      // convenience method used by some tests
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
}

// parseProof helper
export function parseProof(log) {
  return new proof(log);
}

// flexible getter: accepts either a proof instance or a proof log string
export function getTokensForFile(proofOrLog, fname) {
  let p = null;
  if (!proofOrLog) {
    // try to parse sampleLog by default
    p = new proof(sampleLog);
  } else if (typeof proofOrLog === 'string') {
    p = new proof(proofOrLog);
  } else if (typeof proofOrLog === 'object' && typeof proofOrLog.allTokens !== 'undefined') {
    p = proofOrLog;
  } else {
    p = new proof(sampleLog);
  }
  return p.allTokens.filter(t => t.file === fname);
}

/* -------------------------
   Span generator: return HTML fragment STRING (no <pre> wrapper)
   - skips top-level assertions
   - default class name = 'token' (what app.js expects)
   - returns string with newlines preserved
*/
function escapeHtml(str) {
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

export function generateSpansFragment(code, tokens, opts = {}) {
  const skipOverlapping = opts.skipOverlapping !== false;
  const wrapTag = opts.wrapTag || 'span';
  const className = opts.className || 'token'; // default to 'token' to match app.js
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
    if (t.isTopAssertion) continue; // skip top-level assertions
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
    if (cursor < r.startIndex) out += escapeHtml(code.slice(cursor, r.startIndex));
    const inner = code.slice(r.startIndex, r.endIndex);
    const tok = r.token;
    // map CovStatus to UI-friendly string (optional — keep token.CovStatus raw too)
    let statusStr = '';
    if (tok && tok.CovStatus) {
      if (tok.CovStatus === CovStatus.Uncovered || String(tok.CovStatus).toLowerCase().includes('uncover')) statusStr = 'uncovered';
      else if (tok.CovStatus === CovStatus.CovTest || String(tok.CovStatus).toLowerCase().includes('test')) statusStr = 'covered-test';
      else statusStr = 'covered-complete';
    }
    const dataId = escapeHtml(String(tok._key || `${tok.file}:${tok.start.line},${tok.start.col}`));
    const dataStatus = escapeHtml(statusStr);
    const classes = escapeHtml(className);
    const wrapped = `<${wrapTag} class="${classes}" data-id="${dataId}" data-status="${dataStatus}">${escapeHtml(inner)}</${wrapTag}>`;
    out += wrapped;
    cursor = r.endIndex;
  }
  if (cursor < code.length) out += escapeHtml(code.slice(cursor));
  // Return fragment WITHOUT <pre><code> wrapper so app.js can embed it into its own <pre>
  return out;
}
