// spans_provider.js (environment-agnostic)
// Works in browser (as <script>) and in Node (require).

// root: window in browser, global in Node, fallback to a plain object
const root = (typeof window !== 'undefined') ? window
           : (typeof global !== 'undefined') ? global
           : {};

// --- Begin original code but using `root` instead of `window` for attachment ---

root.sampleLog = "";

root.sourceCode = "";

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

    this.allTokens = new Map();
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

        token = new root.prooftoken(file, sLine, sCol, sLine, sCol, proofText, isTopAssertion);
      } else {
        continue;
      }

      if (!this.allTokens.has(token._key)) {
        this.allTokens.set(token._key, token);
      } else {
        token = this.allTokens.get(token._key);
      }
    
      if (isTopAssertion) {
        currentTopAssertion = token;
        if(currentTopAssertion.proofUnusedTokens == null){
            currentTopAssertion.proofUnusedTokens = []; // Assertion appears differently if on top or used in proofs this is for if it appears
                                                        // without ebing on top to make it on top
            currentTopAssertion.proofUsedTokens= [];                                         
            currentTopAssertion.isTopAssertion = true;
        }

        if (!this.topLevelProofInfo.some(t => t._key === token._key)) {
          this.topLevelProofInfo.push(token);
        }
      } else if (currentTopAssertion != null) {
        if (currentBlock === BlockType.ProofDep) {
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
    this.setCoverageStatus(); 
  }

  setCoverageStatus() {
    const allTokensArray = Array.from(this.allTokens.values());


    const allpostcondition = allTokensArray.filter(t => t.prooftext.includes("this postcondition holds"));
    const allensures =  allTokensArray.filter(t => t.prooftext.includes("ensures clause"));

    const allpreconditions =  allTokensArray.filter(t => t.prooftext.includes("method requires clause"));
    const allassertions = allTokensArray.filter(t => t.prooftext.includes("assertion always holds"));  
    const allcodeLines = allTokensArray.filter(t =>
      !allassertions.includes(t) &&
      !allpreconditions.includes(t) &&
      !allpostcondition.includes(t) &&
      !allensures.includes(t)
    );
    // The ones that contain the actual proves
    const allTopTokens =  allTokensArray.filter(t => t.isTopAssertion);


    // Coverage criterios 
    //     Code Lines:
    // - Covered Complete: if used to proof assertions that are postconditons (in proof dependency of them)
    for (let token of allcodeLines) {
      var canexit = false;
      for (const toptoken of allpostcondition){
        for (const tokdependency of toptoken.proofUsedTokens){
          if(token._key == tokdependency._key){
            canexit = true;
            token.CovStatus = CovStatus.CovComplete;
            break
          }
        }
        if(canexit){
          break;
        }
      }
    }
    // - Covered Warning: if used to proof assertions that are not related with postconditions
    //   - This in term represents a bad use case of using formal tools, and if a line was not being covered add an 
    //   assertion only for that line that is not related to the actual function... (this should be a warning)
    //   It is expected that for intance Main method only has warning of this kind
    for (let token of allcodeLines) {
      var canexit = false;
      if(token.CovStatus == CovStatus.CovComplete){
        break;
      }
      for (const toptoken of allTopTokens){
        for (const tokdependency of toptoken.proofUsedTokens){
          if(token._key == tokdependency._key){
            canexit = true;
            token.CovStatus = CovStatus.CovTest;
            break
          }
        }
        if(canexit){
          break;
        }
      }
    }   
    // - Uncovered: Line not use in any assertion/postcondiiton proof (this is the default if not rewritten it is this)


    // Specification Lines:
    // - plain Asserts
    //   - Covered Complete: if used to proof postcondtition
    for (let token of allassertions ) {
      var canexit = false;
      for (const toptoken of allpostcondition){
        if(toptoken._key == token._key){
          continue;
        }
        for (const tokdependency of toptoken.proofUsedTokens){
          if(token._key == tokdependency._key){
            canexit = true;
            token.CovStatus = CovStatus.CovComplete;
            break
          }
        }
        if(canexit){
          break;
        }
      }
    }
    //   - Covered Warning: If used to proof other assertion or itself that need to utilize at least one code line (or assertion that is actually Covered)
    for (let token of allassertions )  {
      var canexit = false;
      if(token.CovStatus == CovStatus.CovComplete){
        break;
      }
      // If top assertion only needs one dependency to be CovStatusComplete
      if(allTopTokens.includes(token)){
        for (const tokdependency of token.proofUsedTokens){
          if(tokdependency.CovStatus == CovStatus.CovComplete){
            token.CovStatus == CovStatus.CovTest;
            break;
          }
        }
      } else {
        // If not top assertion needs to find in any proof dependency it is present a covered line
        for (const toptoken of allTopTokens ){
          let assertion_on_dep = false;
          let covered_line_on_dep = false;
          for (const tokdependency of toptoken.proofUsedTokens){
            if(token._key == tokdependency._key){
              assertion_on_dep = true;
            }
            if(tokdependency.CovStatus == CovStatus.CovComplete){
              covered_line_on_dep = true;
            }
          }
          if(covered_line_on_dep && assertion_on_dep){
            token.CovStatus == CovStatus.CovTest;
            break;
          }
        }
      }
    }  
  
    //   - Uncovered: If used to proof only assertion or itself that do not uses any code lines (likely unecessary specification, only uses other redundant assertions)




    // - postconditions 
    //   - Covered Warning: If for proving the postcondition code lines of the method are used but it is not being used for anything the postcondiiton.
    for (let token of allpostcondition  ) {
      for (const proofToken of token.proofUsedTokens ){
        if(!proofToken.isTopAssertion){
          if(proofToken.CovStatus == CovStatus.CovComplete){
            token.CovStatus = CovStatus.CovTest;
            break;
          }
        }
      }
    }
    for (let token of allensures  ) {
      for (const toptoken of allpostcondition){
        var exit = false;
        for (const proofToken of toptoken.proofUsedTokens ){
          if(token._key == proofToken._key){
              // If ensures used in proving postcondition will be covered simply we can think of semantic afterwards
              exit = true;
              token.CovStatus = CovStatus.CovComplete;
          }
        }
        if(exit){
          break;
        }
      }
    }
    //   - Covered Complete: If for proving the postcondition code lines of the method are used, and the postcondition is used to proof something when that method/function is called. Appears on proof depedencies like so: 
    //     _main_method_that_calls.dfy(9,8)-(9,18): ensures clause at _main_method_that_calls.dfy(2,13)-(2,16) from call
    //   if the postcondition is used to proof something when that method/function is called. Appears on proof depedencies like so: 
    //     _main_method_that_calls.dfy(9,8)-(9,18): ensures clause at _main_method_that_calls.dfy(2,13)-(2,16) from call
   

    // TEMP TO Implement

    //   - Uncovered: No code lines used to prove it (default)
   
   
   
    // TEMP TO Implement
    // - preconditions
    //   - Covered Complete: If precondition is strictly necessary used in proving its own postcondiiton
    for (let token of allpreconditions) {
      var canexit = false;
      for (const toptoken of allpostcondition){
        for (const tokdependency of toptoken.proofUsedTokens){
          if(token._key == tokdependency._key){
            canexit = true;
            token.CovStatus = CovStatus.CovComplete;
            break
          }
        }
        if(canexit){
          break;
        }
      }
    }
    //   - Covered Warning: If precondiiton is used to prove that a call can be made with that fucntion/method appears like so (this appears always like a warning it can indicate that restriction could be maybe removed) :
    //    _main_method_that_calls.dfy(10,8)-(10,19): requires clause at _main_method_that_calls.dfy(3,14)-(3,17) from call
    
    // TEMP TO IMPLEMENT

    //   - Uncovered: precondition not necessary to prove postcondiiton and not being used
  }
};

// environment-aware parseProof:
// - Node: accepts filesystem paths (strings) and returns proof synchronously.
// - Browser: accepts File/Blob objects or content strings or URLs; returns Promise resolving to proof.
root.parseProof = function (dafnyCode ,proofLog) {
    root.sampleLog = proofLog;
    root.sourceCode = dafnyCode;
    return new root.proof(proofLog);
}
  
function internalEscapeHtml(str) {
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

root.generateSpansFragment = function (code, tokens, opts = {}) {
  const skipOverlapping = true;
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
  const tokensArray = Array.from(tokens.values());
  for (const t of tokensArray) {
    if (!t) continue;
    if (!t.start || !t.end) continue;
    const sLine = t.start.line, sCol = t.start.col, eLine = t.end.line, eCol = t.end.col;
    if (!Number.isInteger(sLine) || !Number.isInteger(sCol) || !Number.isInteger(eLine) || !Number.isInteger(eCol)) continue;
    if (sLine < 1 || sLine > lines.length || eLine < 1 || eLine > lines.length) continue;
    const startIndex = lineStart[sLine] + Math.max(0, sCol - 1);
    const endIndex = lineStart[eLine] + eCol;
    if (isNaN(startIndex) || isNaN(endIndex) || startIndex < 0 || endIndex < startIndex) continue;
    ranges.push({ startIndex, endIndex, token: t });
  }

  // Sort by start asc, and for equal starts put the longer range first (so parents come before children)
  ranges.sort((a, b) => a.startIndex - b.startIndex || b.endIndex - a.endIndex);

  // Build nested tree of ranges (only allow nesting when fully contained).
  // If skipOverlapping is true, partially-overlapping ranges are skipped.
  const roots = [];
  const stack = [];
  for (const r of ranges) {
    // pop finished stack frames
    while (stack.length && r.startIndex >= stack[stack.length - 1].endIndex) stack.pop();

    if (stack.length === 0) {
      // no parent -> root
      r.children = [];
      roots.push(r);
      stack.push(r);
    } else {
      const parent = stack[stack.length - 1];
      if (r.endIndex <= parent.endIndex) {
        // fully contained -> nested child
        r.children = [];
        if (!parent.children) parent.children = [];
        parent.children.push(r);
        stack.push(r);
      } else {
        // partial overlap: start inside parent but ends after parent -> ambiguous
        if (skipOverlapping) {
          // skip this range to keep well-formed nested HTML
          continue;
        } else {
          // if not skipping overlapping, add it as a sibling/root at the outermost level where it doesn't start inside
          // find level to attach as sibling (pop until we find a frame that ends <= r.startIndex)
          let attached = false;
          // try to pop until we can attach as root/sibling
          let tempStack = stack.slice();
          while (tempStack.length) {
            if (r.startIndex >= tempStack[tempStack.length - 1].endIndex) {
              tempStack.pop();
            } else break;
          }
          if (tempStack.length === 0) {
            r.children = [];
            roots.push(r);
            stack.length = 0;
            stack.push(r);
            attached = true;
          }
          if (!attached) {
            // fallback: skip to avoid invalid HTML
            continue;
          }
        }
      }
    }
  }

  // helper to produce attributes for a token
  function tokenAttrs(tok) {
    let statusStr = '';
    if (tok && tok.CovStatus) {
      if (tok.CovStatus === root.CovStatus.Uncovered) statusStr = 'uncovered';
      else if (tok.CovStatus === root.CovStatus.CovTest) statusStr = 'covered-test';
      else statusStr = 'covered-complete';
    }
    const dataId = internalEscapeHtml(String(tok._key || `${tok.file}:${tok.start.line},${tok.start.col}`));
    const dataStatus = internalEscapeHtml(statusStr);
    const classes = internalEscapeHtml(className);
    const istopAttr = tok.isTopAssertion ? ' data-istop="true"' : '';
    return { dataId, dataStatus, classes, istopAttr };
  }

  // recursive renderer for a node and its children
  function renderNode(node) {
    const tok = node.token;
    const { dataId, dataStatus, classes, istopAttr } = tokenAttrs(tok || {});
    let innerOut = '';
    let cursor = node.startIndex;
    if (node.children && node.children.length) {
      // ensure children are sorted by startIndex
      node.children.sort((a, b) => a.startIndex - b.startIndex);
      for (const child of node.children) {
        if (cursor < child.startIndex) innerOut += internalEscapeHtml(code.slice(cursor, child.startIndex));
        innerOut += renderNode(child);
        cursor = child.endIndex;
      }
    }
    if (cursor < node.endIndex) innerOut += internalEscapeHtml(code.slice(cursor, node.endIndex));
    // wrap and return (innerOut already escaped)
    return `<${wrapTag} class="${classes}" data-id="${dataId}" ${istopAttr} data-status="${dataStatus}">${innerOut}</${wrapTag}>`;
  }

  // render roots sequentially
  let out = '';
  let cursor = 0;
  roots.sort((a, b) => a.startIndex - b.startIndex);
  for (const rootNode of roots) {
    if (cursor < rootNode.startIndex) out += internalEscapeHtml(code.slice(cursor, rootNode.startIndex));
    out += renderNode(rootNode);
    cursor = rootNode.endIndex;
  }
  if (cursor < code.length) out += internalEscapeHtml(code.slice(cursor));
  return out;
};

root.getDependsOn = function (key, proof) {
  if (!proof.allTokens.has(key)) {
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
  if (!proof.allTokens.has(key)) {
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

root.getSampleLog = function(){
  return root.sampleLog;
}

root.getSourceCode = function(){
  return root.sourceCode;
}

// --- End original code ---

// If running under Node (CommonJS), export named symbols for unit tests
if (typeof module !== 'undefined' && typeof module.exports !== 'undefined') {
  module.exports = {
    getSampleLog: root.sampleLog,
    getSourceCode: root.sourceCode,
    targetFileName: root.targetFileName,
    CovStatus: root.CovStatus,
    TokenType: root.TokenType,
    prooftoken: root.prooftoken,
    proof: root.proof,
    parseProof: root.parseProof,
    generateSpansFragment: root.generateSpansFragment,
    getDependsOn: root.getDependsOn,
    getUsedOn: root.getUsedOn,
  };
}




// import { createRequire } from 'module';
// const require = createRequire(import.meta.url);
// const fs = require('fs');

// const proofFile = "src/prover_log.txt";
// const sourceFile = "src/source_code.dfy";

// const src = fs.readFileSync(sourceFile, "utf-8");   // <-- make this a string
// const log = fs.readFileSync(proofFile, "utf-8");    // <-- make this a string

// const proof = root.parseProof(src, log);
// let b = 3;