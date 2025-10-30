// proof_parser.js
// Pure parsing & model logic. No DOM code here.
// Exports: parseReport, Profile, ProfileFile, Element, runTests

export class Element {
  constructor(file, sLine, sCol, eLine, eCol, text, key) {
    this.file = file;
    this.start = { line: sLine, col: sCol };
    this.end = { line: eLine, col: eCol };
    this.text = text;
    this._key = key;
  }

  coversPos(line, col) {
    if (line < this.start.line || line > this.end.line) return false;
    if (this.start.line === this.end.line) return col >= this.start.col && col <= this.end.col;
    if (line === this.start.line) return col >= this.start.col;
    if (line === this.end.line) return col <= this.end.col;
    return true;
  }

  // assertion -> proofDependencies, plus siblings before
  uses(profileFile) {
    const results = [];
    const seen = new Set();
    for (const batch of profileFile.batches) {
      if (batch.assertions.includes(this._key)) {
        for (const dKey of batch.proofDependencies) {
          if (!seen.has(dKey)) { seen.add(dKey); results.push(profileFile.elements.get(dKey)); }
        }
      }
      const myIdx = batch.proofDependencies.indexOf(this._key);
      if (myIdx !== -1) {
        for (let i = 0; i < myIdx; i++) {
          const s = batch.proofDependencies[i];
          if (!seen.has(s)) { seen.add(s); results.push(profileFile.elements.get(s)); }
        }
      }
    }
    return results.filter(Boolean);
  }

  // proofDependency -> assertions, plus siblings after
  usedBy(profileFile) {
    const results = [];
    const seen = new Set();
    for (const batch of profileFile.batches) {
      if (batch.proofDependencies.includes(this._key)) {
        for (const aKey of batch.assertions) {
          if (!seen.has(aKey)) { seen.add(aKey); results.push(profileFile.elements.get(aKey)); }
        }
        const myIdx = batch.proofDependencies.indexOf(this._key);
        if (myIdx !== -1) {
          for (let j = myIdx + 1; j < batch.proofDependencies.length; j++) {
            const s = batch.proofDependencies[j];
            if (!seen.has(s)) { seen.add(s); results.push(profileFile.elements.get(s)); }
          }
        }
      }
    }
    return results.filter(Boolean);
  }

  spanString() {
    return `(${this.start.line},${this.start.col})-(${this.end.line},${this.end.col})`;
  }
}

export class Batch {
  constructor(number) {
    this.number = number;
    this.assertions = [];
    this.proofDependencies = [];
    this.unusedByProof = [];
    this.assertionStrings = [];
  }
}

export class ProfileFile {
  constructor(name) {
    this.name = name;
    this.elements = new Map();
    this.batches = [];
  }

  getElementAtPos(line, col) {
    let best = null;
    let bestSize = Infinity;
    for (const el of this.elements.values()) {
      if (el.coversPos(line, col)) {
        const size = (el.end.line - el.start.line) * 10000 + (el.end.col - el.start.col);
        if (size < bestSize) { best = el; bestSize = size; }
      }
    }
    return best;
  }

  findElementsContainingToken(tokenText, line) {
    const matches = [];
    if (!tokenText) return matches;
    for (const el of this.elements.values()) {
      if (el.text && el.text.indexOf(tokenText) !== -1) matches.push(el);
    }
    const onLine = matches.filter(e => e.coversPos(line, 1));
    if (onLine.length) {
      onLine.sort((a, b) => ((a.end.line - a.start.line) * 10000 + (a.end.col - a.start.col)) - ((b.end.line - b.start.line) * 10000 + (b.end.col - b.start.col)));
      return onLine;
    }
    matches.sort((a, b) => ((a.end.line - a.start.line) * 10000 + (a.end.col - a.start.col)) - ((b.end.line - b.start.line) * 10000 + (b.end.col - b.start.col)));
    return matches;
  }
}

export class Profile {
  constructor() { this.files = new Map(); }
  getFile(name) { return this.files.get(name); }
  _ensureElement(fileName, sLine, sCol, eLine, eCol, text) {
    const key = `${fileName}@${sLine}:${sCol}-${eLine}:${eCol}`;
    if (!this.files.has(fileName)) this.files.set(fileName, new ProfileFile(fileName));
    const pf = this.files.get(fileName);
    if (!pf.elements.has(key)) {
      pf.elements.set(key, new Element(fileName, sLine, sCol, eLine, eCol, text, key));
    }
    return pf.elements.get(key);
  }
}

/** parseReport(text) -> Profile
 *  Parses the textual Dafny verifier report into Profile objects.
 *  Behavior: robust to point and range entries (file(line,col) and file(line,col)-(line,col)).
 */
export function parseReport(text) {
  const profile = new Profile();
  const lines = text.split(/\r?\n/);
  let currentBatch = null;
  let currentSection = null;
  let currentProfileFileNameGuess = null;

  function addEntry(entry, batch, section) {
    const rangeRe = /^ *(.+?)\((\d+),\s*(\d+)\)-\((\d+),\s*(\d+)\):\s*(.+)$/;
    const pointRe = /^ *(.+?)\((\d+),\s*(\d+)\):\s*(.+)$/;
    let m = entry.match(rangeRe);
    if (m) {
      const file = m[1].trim();
      const sLine = parseInt(m[2], 10), sCol = parseInt(m[3], 10);
      const eLine = parseInt(m[4], 10), eCol = parseInt(m[5], 10);
      const desc = m[6].trim();
      const el = profile._ensureElement(file, sLine, sCol, eLine, eCol, desc);
      if (section === 'assertions') batch.assertions.push(el._key);
      else if (section === 'deps') batch.proofDependencies.push(el._key);
      else if (section === 'unused') batch.unusedByProof.push(el._key);
      return;
    }
    m = entry.match(pointRe);
    if (m) {
      const file = m[1].trim();
      const sLine = parseInt(m[2], 10), sCol = parseInt(m[3], 10);
      const desc = m[4].trim();
      const el = profile._ensureElement(file, sLine, sCol, sLine, sCol, desc);
      if (section === 'assertions') batch.assertions.push(el._key);
      else if (section === 'deps') batch.proofDependencies.push(el._key);
      else if (section === 'unused') batch.unusedByProof.push(el._key);
      return;
    }

    // fallback: pseudo element
    const file = currentProfileFileNameGuess || 'unknown';
    const el = profile._ensureElement(file, 0, 0, 0, 0, entry.trim());
    if (section === 'assertions') batch.assertions.push(el._key);
    else if (section === 'deps') batch.proofDependencies.push(el._key);
    else if (section === 'unused') batch.unusedByProof.push(el._key);
  }

  for (let i = 0; i < lines.length; i++) {
    const raw = lines[i];
    const line = raw.replace(/\t/g, '    ');
    const batchMatch = line.match(/^\s*Assertion batch\s+(\d+)\s*:/i);
    if (batchMatch) {
      currentBatch = new Batch(parseInt(batchMatch[1], 10));
      currentSection = null;
      currentProfileFileNameGuess = null;
      continue;
    }

    if (!currentBatch) continue;

    const sec = line.trim();
    if (/^Assertions:\s*$/i.test(sec)) { currentSection = 'assertions'; continue; }
    if (/^Proof dependencies:\s*$/i.test(sec)) { currentSection = 'deps'; continue; }
    if (/^Unused by proof:\s*$/i.test(sec)) { currentSection = 'unused'; continue; }

    if (currentSection && /^\s{4,}[_A-Za-z0-9\/\.\-\\].*$/.test(line)) {
      const entry = line.trim();
      const fileGuess = entry.match(/^(.+?)\(/);
      if (fileGuess) currentProfileFileNameGuess = fileGuess[1].trim();
      if (currentSection === 'assertions') currentBatch.assertionStrings.push(entry);
      addEntry(entry, currentBatch, currentSection);
      continue;
    }

    if (currentBatch && /^\s*$/.test(line)) {
      if (currentBatch.assertions.length || currentBatch.proofDependencies.length || currentBatch.unusedByProof.length) {
        const fileNames = new Set();
        for (const key of [...currentBatch.assertions, ...currentBatch.proofDependencies, ...currentBatch.unusedByProof]) {
          const fn = key.split('@', 1)[0];
          fileNames.add(fn);
        }
        if (fileNames.size === 0) {
          const gf = currentProfileFileNameGuess || 'unknown';
          if (!profile.files.has(gf)) profile.files.set(gf, new ProfileFile(gf));
          profile.files.get(gf).batches.push(currentBatch);
        } else {
          for (const fn of fileNames) {
            if (!profile.files.has(fn)) profile.files.set(fn, new ProfileFile(fn));
            profile.files.get(fn).batches.push(currentBatch);
          }
        }
      }
      currentBatch = null;
      currentSection = null;
    }
  }

  if (currentBatch) {
    const fileNames = new Set();
    for (const key of [...currentBatch.assertions, ...currentBatch.proofDependencies, ...currentBatch.unusedByProof]) {
      const fn = key.split('@', 1)[0];
      fileNames.add(fn);
    }
    const gf = currentProfileFileNameGuess || 'unknown';
    if (fileNames.size === 0) {
      if (!profile.files.has(gf)) profile.files.set(gf, new ProfileFile(gf));
      profile.files.get(gf).batches.push(currentBatch);
    } else {
      for (const fn of fileNames) {
        if (!profile.files.has(fn)) profile.files.set(fn, new ProfileFile(fn));
        profile.files.get(fn).batches.push(currentBatch);
      }
    }
  }

  return profile;
}

/** runTests()
 *  Runs internal tests on the default sample input and returns an array of result strings.
 *  Does not touch the DOM; throws on failure (or returns messages).
 */
export function runTests() {
  const sample = `Results for Abs (correctness)
  Assertion batch 1:
    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20): this postcondition holds
    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20)-(2,23): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(12,5)-(12,15): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(16,1)-(18,1): function definition for Id
    Unused by proof:
      _USECASE_find_irrelevant_lines_for_proof.dfy(6,5)-(6,11): assignment (or return)

  Assertion batch 2:
    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19): this postcondition holds
    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19)-(3,24): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(10,5)-(10,12): assignment (or return)
`;
  const p = parseReport(sample);
  const fname = '_USECASE_find_irrelevant_lines_for_proof.dfy';
  const pf = p.getFile(fname);
  const results = [];
  if (!pf) { results.push('FAIL: expected profile file'); return results; }

  // test element covering (3,21)
  const el321 = pf.getElementAtPos(3, 21);
  if (!el321) throw new Error('Test failed: element covering (3,21) not found');
  results.push(`OK: found element ${el321.spanString()}`);

  // test usedBy
  const usedBy = el321.usedBy(pf);
  if (!Array.isArray(usedBy) || usedBy.length === 0) throw new Error('Test failed: usedBy empty');
  results.push('OK: usedBy non-empty');

  // test uses for assertion at (3,19)
  const assertion319 = pf.getElementAtPos(3, 19);
  if (!assertion319) throw new Error('Test failed: assertion at (3,19) not found');
  const uses = assertion319.uses(pf);
  if (!uses.some(e => e.start.line === 10 && e.start.col === 5)) throw new Error('Test failed: expected use (10,5)');

  results.push('OK: assertion uses contain (10,5)');

  return results;
}

// auto-run tests in Node environment for quick CLI verification
if (typeof window === 'undefined') {
  try {
    const res = runTests();
    console.log('Parser tests OK:', res);
  } catch (err) {
    console.error('Parser tests FAILED:', err);
  }
}
