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
  Uncovered: "Uncovered"
};

root.TokenType = {
  Undefined: "Undefined", // Not yet evaluated
  Precondition: "Precondition",
  Postcondition: "Postcondition",
  AssertionManual: "AssertionManual",
  AssertionAutomatic: "AssertionAutomatic",
  CodeLine: "CodeLine"
};

    // Top
    // A1 A2 A3 A4

    // A2
    // A5 A6 A10

    // A6
    // A10 A4

    // Faz sentido
    // Top
    // this.provedBy(A1,A2,A3,A4)

    // A2
    // proves(Top)
    // provedBy(A5,A6,A10)

    // A6
    // proves(A2)
    // provedBy(A10,A4)

    //A10
    // proves(A6,A2)
    // provedBy(todo etc etc)

    //etc

class Node {
  constructor(file, sLine, sCol, eLine, eCol, prooftext, isTopAssertion) {
    this.file = file;
    this.prooftext = prooftext;
    this.start = { line: sLine, col: sCol };
    this.end = { line: eLine, col: eCol };

    this.isTopAssertion = isTopAssertion;
    if(this.isTopAssertion){
      this.topAliasNode = null;
    }

    this.CovStatus = root.CovStatus.Uncovered;
    this.CovStatusInternal = root.CovStatus.Uncovered;

    this.tokenType = root.TokenType.Undefined;

    this.id = `${this.file}:${this.start.line},${this.start.col}-${this.end.line},${this.end.col}`;

    this.proves = new Set(); 
    this.provedBy = new Set(); 

    this.type = root.TokenType.Undefined;

    this.updateIsTopAssertion(isTopAssertion);
  }

  updateIsTopAssertion(isTopAssertion){
    this.isTopAssertion = isTopAssertion;
    if(this.prooftext.includes("this postcondition holds")){
      this.type = root.TokenType.Postcondition;
    } else if(this.prooftext.includes("ensures clause")){
      this.type = root.TokenType.Postcondition;
    } else if(this.prooftext.includes("method requires clause")){
      this.type = root.TokenType.Precondition;
    } else if(this.prooftext.includes("assertion always holds")){
      this.type = root.TokenType.AssertionManual;
    } else if(this.prooftext.includes("index in range") || 
              this.prooftext.includes("target object is never null")||
              this.prooftext.includes("which is subject to definite-assignment rules, is always initialized at this return point") ||
              this.prooftext.includes("which is subject to definite-assignment rules, is always initialized here")
             ){
              // Heuristic (if index in range is an automatic assertion safe to treat less severely)
      this.type = root.TokenType.AssertionAutomatic;
    } else if(this.isTopAssertion){
      this.type = root.TokenType.AssertionAutomatic;
    } else {
      this.type = root.TokenType.CodeLine;
    }
  }

  connectTo(target) {
    this.provedBy.add(target);
    target.proves.add(this);
  }
}

class ProofGraph {
  constructor(){
    this.nodes = new Map(); //id -> Node 
    this.topNodes = new Map(); //id-> Node (for the top nodes, main assertions on proof)
  }

  addNode(node){
    this.nodes.set(node.id, node);
  }

  getNode(id){
    return this.nodes.get(id);
  }


  hasNode(id){
    return this.nodes.has(id);
  }


  addTopNode(node){
    this.topNodes.set(node.id, node);
  }

  getTopNode(id){
    return this.topNodes.get(id);
  }


  hasTopNode(id){
    return this.topNodes.has(id);
  }


  addEdge(fromId, toId){
    const from = this.getNode(fromId);
    const to = this.getNode(toId);
    if(!from || !to){
          throw new Error(`Invalid edge: ${fromId} -> ${toId}`);
    }
    from.connectTo(to);  
  }

  getAllNodes() {
    return Array.from(this.nodes.values());
  }

  getAllTopNodes(){
    return Array.from(this.topNodes.values());
  }


  // I only am using getAll=1, if not I was losing matches 
  // Nevertheless I may need to isolate this for more functions etc but for now seems good

  getBFSneighbors(key, isProvedBy, getAll=0){
    if (!this.hasNode(key)) {
      return null;
    }

    const token = this.getNode(key);
    let neighbors = new Set();

    const queue = [{ node: token}];
    const visited = new Set([token.id]); 

    while (queue.length > 0) {
      const {node} = queue.shift();
      let targetSet = []
      if(getAll){
        targetSet = new Set([...node.provedBy, ...node.proves]);
      } else {
        if(isProvedBy){
          targetSet = node.provedBy
        } else {
          targetSet = node.proves
        }
      }
      for (const pred of targetSet) {
        if (visited.has(pred.id)) {
          continue;
        }
        visited.add(pred.id);
        neighbors.add(pred);
        queue.push({ node: pred});
      }
    }
    return  [...neighbors]; 
  } 
}

class Proof {
  constructor(proofLog, sourceCode){
    this.proofGraph = new ProofGraph();
    
    const BlockType = { NoBlock: 0, Assertion: 1, ProofDep: 2, Unused: 3 };
    const lines = proofLog.split(/\r?\n/);
   
    let assertionBatch = null;
    let currentTopAssertion = null;
    let currentBlock = BlockType.NoBlock;
    this.topLevelProofInfo = [];
    this.lineStatus = [];

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
        /// Update necessary in case same assertion is used as top and as proof dependenct, If dependency appears
        // first it is needed to change assertion type to top
        currentTopAssertion.updateIsTopAssertion(isTopAssertion);

        if(!this.proofGraph.hasTopNode(token.id)){
          this.proofGraph.addTopNode(token);
        }  
      } else if (currentTopAssertion != null) {
        if (currentBlock === BlockType.ProofDep) {
          // Top assertion is registered with only a single carachter even though the actual assertion or postcondition etc
          // occupies on the proof dependecnies its correct place 
          // What I should do is change that token when i noticed that i am on the correct token
          if( (token.start.line <= currentTopAssertion.start.line) && 
              (currentTopAssertion.start.line <= token.end.line) && 
              (token.start.col <= currentTopAssertion.start.col) && 
              (currentTopAssertion.start.col <= token.end.col)) {
                // Top Assertions retain the alias node that represents itself but with the full range of tokens
                // This is usefull to get more complex semantics specially when using potcondition and preconditions in
                // methods function calls
                currentTopAssertion.topAliasNode = token;
              }
        



          // Note addEdge is resilient to repetition of edged
          this.proofGraph.addEdge(currentTopAssertion.id, token.id);
          // if The current assertion text has something like so
          //  test_fully_use_postcondition.dfy(7,6)-(7,19): ensures clause at test_fully_use_postcondition.dfy(2,13)-(2,16) from call
          // I have to parse second part as well and add a connection from test_fully_use_postcondition.dfy(7,6)-(7,19) to test_fully_use_postcondition.dfy(2,13)-(2,16) to 
       
           const postcall = /ensures clause at\s+([^\s()]+)\((\d+),(\d+)\)-\((\d+),(\d+)\)/;

           const m = line.match(postcall);
           //  console.log("AMEN AMEN 2");
           if(m){
            const file = m[1].trim();
            const sLine = parseInt(m[2], 10);
            const sCol = parseInt(m[3], 10);
            const eLine = parseInt(m[4], 10);
            const eCol = parseInt(m[5], 10);

            // Create token if not exists
            let posttoken = new Node(file, sLine, sCol, eLine, eCol, "Post called externally", isTopAssertion);
            if (!this.proofGraph.hasNode(posttoken.id)) {
              this.proofGraph.addNode(posttoken);
            } else {
              posttoken = this.proofGraph.getNode(posttoken.id);
            }
            // Connect token
            this.proofGraph.addEdge(token.id, posttoken.id);
           }
        }
      }
    }
    this.setCoverageStatus(); 
    this.setLineStatus(sourceCode);
  }
    
  setLineStatus(code){
    const tokens = this.proofGraph.getAllNodes();
    const lines = code.split('\n');
    this.lineStatus = new Array(lines.length).fill(CovStatus.CovComplete);
    if (!tokens || tokens.length === 0) return;
    for (const t of tokens) {
        if (!t || !t.start || !t.end) continue;
        const sLine = Math.max(1, t.start.line || 1);
        const mapped = t.CovStatus;
        const idx =  sLine  - 1;
        if (this.lineStatus[idx] === CovStatus.Uncovered){
           continue;
        } if (mapped === CovStatus.Uncovered) {
          this.lineStatus[idx] = CovStatus.Uncovered;
        } else if (mapped === CovStatus.CovTest && this.lineStatus[idx] !== CovStatus.Uncovered){
           this.lineStatus[idx] = CovStatus.CovTest;
        }
    }
  }

  setCoverageStatus() {
    // Internally all lines are threated the same CovStatusInternal
    // If line appears on the dependency graph of a postcondition it is covered 
    // else if line appears on the dependency graph of another top assertion it is CovTest
    // else it is uncovered
    // Top level postcondiiton are aways covComplte internally (as they are proved)
    // Top level assertions are aways covTest internally unless covComplete (as they are proved)
    const allTopTokensArray =  this.proofGraph.getAllTopNodes();
    // Set the Cov Complete
    const allPostconditions = allTopTokensArray.filter(t => t.type == root.TokenType.Postcondition);
    for (const post of allPostconditions) {
      post.CovStatusInternal = CovStatus.CovComplete;
      const  postneighbors = this.proofGraph.getBFSneighbors(post.id , 1,1);  
      for (let neigh of postneighbors){
         neigh.CovStatusInternal = CovStatus.CovComplete;
      }
    }
    // Set the Cov Test 
    const allTopNotPost = allTopTokensArray.filter(t => t.type != root.TokenType.Postcondition);
    for (const post of allTopNotPost) {
      post.CovStatusInternal = CovStatus.CovComplete;
      const  postneighbors = this.proofGraph.getBFSneighbors(post.id , 1,1);  
      for (let neigh of postneighbors){
        if(neigh.CovStatusInternal != CovStatus.CovComplete){
            neigh.CovStatusInternal = CovStatus.CovTest;
        }
      }
    }

    // TEMP consider equal semantics
    //const allTokensArray =  this.proofGraph.getAllNodes();
    //for(let token of allTokensArray){
    //  token.CovStatus = token.CovStatusInternal;
    //}
    
    // SEMANTICS

    // CODE LINES
    //   CovComplete: If line appears on the dependency graph of a postcondition it is covered else
    //   CovTest: if line appears on the dependency graph of another top assertion it is CovTest
    //   Uncovered: Rest
    //   Equal semantics to CovInternal

    const allTokensArray =  this.proofGraph.getAllNodes();
    const allCodeLines = allTokensArray.filter(t => t.type == root.TokenType.CodeLine);
    for(let token of allCodeLines){
      token.CovStatus = token.CovStatusInternal;
    }

    // AUTOMATIC ASSERTIONS (always set to Covered)
    //  CovStatusInternal=Complete -> CovStatus=Complete
    //  CovStatusInternal=CovTest -> CovStatus=Complete
    //  CovStatusInternal=Uncovered -> CovStatus=Complete
    const allAutoAssertions = allTokensArray.filter(t => t.type == root.TokenType.AssertionAutomatic);
    for(let token of allAutoAssertions){
      token.CovStatus = CovStatus.CovComplete;
    }
    // Manual Assertion (same semantic as internal)
    //  CovStatusInternal=Complete -> CovStatus=Complete
    //  CovStatusInternal=CovTest -> Uncovered
    //  CovStatusInternal=Uncovered -> Uncovered 

    // But this causes a impossibily: Manual assertions are always top 
    // Therefore they can be proven by themselves if tautologies 
    // If signalled as CovTest it should be considered uncovered in my view
    // As it is not used in postcondiitons 
    // This prenets tatutoliges (and makes to be impossible to have manual assertion flagged as covTest)

    const allManualAssertions = allTokensArray.filter(t => t.type == root.TokenType.AssertionManual);
    for(let token of allManualAssertions){
      if(token.CovStatusInternal == CovStatus.CovComplete){
         token.CovStatus = CovStatus.CovComplete;
      } else {
         token.CovStatus = CovStatus.Uncovered;
      }
    }
    // Precondiiton
    // CovComplete -> - it is on the direct graph of a postcondition (if CovCompleteInternal)
    // CovTest     ->   used in a method call (Dependency graph must have proof by in another method (need to check how to acomplish this))
    //             ->   used to prove asserts not related to postcondiiton (assert that are CovTest)
    //                 (these coV tests probaly are equivalnet to covStatusInternal semantics)
    const allPreconditions = allTokensArray.filter(t => t.type == root.TokenType.Precondition);
    for(let token of allPreconditions){
      token.CovStatus = token.CovStatusInternal;
    }
    // Postcondition
    // CovComplete -> (1) Its direct graph is called by another things. and it uses manualAssetion or codeLines that is marked as CovComplete ()
    // CovTest     -> It is not called by other methods. But it uses manual assertions or codelines that are marked has CodeComplete or preconditions
    // Uncovered   -> It is not used by any code lines or assertions that are not automatic or preconditions. (It is a axiom basically 1==1)
    // Only for the top ones
    for(let post of allPostconditions){
      const  postneighbors = this.proofGraph.getBFSneighbors(post.id , 1);  
      // If any of its depedncies is not a postcondition and is covered he is CovTest at least
      let anychildIsCovComplete = false;
      for(let neigh of postneighbors){
        if(neigh.type != root.TokenType.Postcondition && neigh.CovStatus == CovStatus.CovComplete){
          anychildIsCovComplete = true;
          break;
        }
      }
      let anyParents = false;
      // Alias needed has actual relantionship of use uses alias instead of top not specified range condition
      const alias = post.topAliasNode;
      if(alias){
        const postParents = this.proofGraph.getBFSneighbors(alias.id, 0);
     
        if(postParents.length > 1){
          // one as parent for sure is at minimum the top postcondition (parent of the alias) 
          anyParents = true;
        }
      }
      if(anyParents && anychildIsCovComplete){
          post.CovStatus = CovStatus.CovComplete;
      } else if(anychildIsCovComplete){
          post.CovStatus = CovStatus.CovTest;
      } else {
          post.CovStatus = CovStatus.Uncovered;
      }
    }
    // for the nonTopOnes they can get they internall value
    const allPostconditionsNonTop = allTokensArray.filter(t => t.type == root.TokenType.Postcondition && t.isTopAssertion == false);
    for(let token of allPostconditionsNonTop){
      token.CovStatus = token.CovStatusInternal;
    }
    return;
  }
};

// environment-aware parseProof:
// - Node: accepts filesystem paths (strings) and returns proof synchronously.
// - Browser: accepts File/Blob objects or content strings or URLs; returns Promise resolving to proof.
root.parseProof = function (dafnyCode ,proofLog) {
    root.sampleLog = proofLog;
    root.sourceCode = dafnyCode;
    return new Proof(proofLog, dafnyCode);
}
  
function internalEscapeHtml(str) {
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

root.generateSpansFragment = function (code, proof) {
  const skipOverlapping = true;
  const wrapTag =  'span';
  const className = 'token';
  const lines = code.split('\n');
  const lineStart = new Array(lines.length + 2);
  let pos = 0;
  for (let i = 0; i < lines.length; ++i) {
    lineStart[i + 1] = pos;
    pos += lines[i].length + 1;
  }

  const ranges = [];
  const tokensArray = proof.proofGraph.getAllNodes();
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
    const dataId = internalEscapeHtml(tok.id);
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
  if (!proof.proofGraph.hasNode(key)) {
    return null;
  }

  return proof.proofGraph.getBFSneighbors(key, 0, 1);
} 

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
  };
}