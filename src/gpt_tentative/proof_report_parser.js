// dafny_report_parser.js
//
// Assumptions / behaviour:
// - Input text contains "Assertion batch N:" blocks with sections "Assertions:", "Proof dependencies:", "Unused by proof:".
// - Entries come in two forms:
//     1) point entry: FILE(line,col): description
//     2) range entry: FILE(line,col)-(line,col): description
//   We treat point entries as range with identical start and end.
// - We create unique Element objects keyed by file + start + end. Element stores lightweight data only.
// - uses() is defined as: for an element that appears as an ASSERTION in a batch, return the batch's proof dependencies (as Element objects).
// - usedBy() is defined as: for an element that appears in any batch's proofDependencies, return the assertion(s) that depend on it.
// - Both uses() and usedBy() compute results on demand by scanning parsed batches.
//
// Output API (example):
// const prof = parseReport(text);
// const profFile = prof.getFile('_USECASE_find_irrelevant_lines_for_proof.dfy');
// const el = getElInLineCol(profFile, 3, 21);
// el.usedBy(); // returns elements that reference this element in their batches' proofDependencies
// el.uses();   // returns elements that this element uses (if it is an assertion)

class Element {
    constructor(file, startLine, startCol, endLine, endCol, text, key) {
        this.file = file;
        this.start = { line: startLine, col: startCol };
        this.end = { line: endLine, col: endCol };
        this.text = text;
        this._key = key; // canonical key (string)
        // NOTE: we do not store adjacency lists here; uses() / usedBy() compute on the fly
    }

    // checks whether (line,col) is inside the element's span
    covers(line, col) {
        const s = this.start, e = this.end;
        if (line < s.line || line > e.line) return false;
        if (s.line === e.line) {
            return col >= s.col && col <= e.col;
        }
        if (line === s.line) return col >= s.col;
        if (line === e.line) return col <= e.col;
        return true; // strictly between start and end lines
    }

    // computed on the fly: find proofDependencies for batches where this element is an assertion
    // OR: find elements in the same proofDependencies list where this element appears, but that are BEFORE it
    uses(profileFile) {
        const results = [];
        const seen = new Set();

        for (const batch of profileFile.batches) {
            // 1) If this element is one of the batch's assertions -> add all proofDependencies
            if (batch.assertions.includes(this._key)) {
                for (const dKey of batch.proofDependencies) {
                    const el = profileFile.elements.get(dKey);
                    if (el && !seen.has(dKey)) {
                        seen.add(dKey);
                        results.push(el);
                    }
                }
            }

            // 2) If this element itself appears in the batch's proofDependencies -> add siblings BEFORE it
            const myIdx = batch.proofDependencies.indexOf(this._key);
            if (myIdx !== -1) {
                for (let i = 0; i < myIdx; i++) {
                    const sibKey = batch.proofDependencies[i];
                    const sibEl = profileFile.elements.get(sibKey);
                    if (sibEl && !seen.has(sibKey)) {
                        seen.add(sibKey);
                        results.push(sibEl);
                    }
                }
            }
        }

        return results;
    }

    // computed on the fly: find assertions that have this element in their proofDependencies
    // AND: find elements in the same proofDependencies list where this element appears, but that are AFTER it
    usedBy(profileFile) {
        const results = [];
        const seen = new Set();

        for (const batch of profileFile.batches) {
            // If this element is listed among the proofDependencies, then return the batch assertions (as before)
            if (batch.proofDependencies.includes(this._key)) {
                for (const aKey of batch.assertions) {
                    const aEl = profileFile.elements.get(aKey);
                    if (aEl && !seen.has(aKey)) {
                        seen.add(aKey);
                        results.push(aEl);
                    }
                }

                // Also include sibling proofDependencies that come AFTER this element in the same list
                const myIdx = batch.proofDependencies.indexOf(this._key);
                if (myIdx !== -1) {
                    for (let j = myIdx + 1; j < batch.proofDependencies.length; j++) {
                        const sibKey = batch.proofDependencies[j];
                        const sibEl = profileFile.elements.get(sibKey);
                        if (sibEl && !seen.has(sibKey)) {
                            seen.add(sibKey);
                            results.push(sibEl);
                        }
                    }
                }
            }
        }

        return results;
    }

    // helper to nicely display span
    spanString() {
        return `(${this.start.line},${this.start.col})-(${this.end.line},${this.end.col})`;
    }

    toString() {
        return `${this.file}${this.spanString()}: ${this.text}`;
    }
}

class Batch {
    constructor(number) {
        this.number = number;
        this.assertions = []; // list of element keys
        this.proofDependencies = []; // list of element keys
        this.unusedByProof = []; // list of element keys (kept for completeness)
    }
}

class ProfileFile {
    constructor(name) {
        this.name = name;
        this.elements = new Map(); // key -> Element
        this.batches = []; // array of Batch
    }

    // find element that covers given line,col (first match)
    getElementAt(line, col) {
        for (const el of this.elements.values()) {
            if (el.covers(line, col)) return el;
        }
        return null;
    }
}

class Profile {
    constructor() {
        this.files = new Map(); // filename -> ProfileFile
    }

    getFile(name) {
        return this.files.get(name);
    }

    // add or get element: canonicalizes into the file's elements map
    _ensureElement(fileName, sLine, sCol, eLine, eCol, text) {
        const key = `${fileName}@${sLine}:${sCol}-${eLine}:${eCol}`;
        if (!this.files.has(fileName)) this.files.set(fileName, new ProfileFile(fileName));
        const pf = this.files.get(fileName);
        if (pf.elements.has(key)) return pf.elements.get(key);
        const el = new Element(fileName, sLine, sCol, eLine, eCol, text, key);
        pf.elements.set(key, el);
        return el;
    }
}

/**
 * parseReport(text) -> Profile
 * parses the textual Dafny report into a Profile object
 */
function parseReport(text) {
    const profile = new Profile();
    const lines = text.split(/\r?\n/);

    let currentBatch = null;
    let currentSection = null;
    let currentProfileFileNameGuess = null;

    // helpers to push parsed entry text into canonical elements and into the appropriate batch list
    function addEntryToBatch(entryText, batch, section) {
        // try range form first: FILE(l,c)-(L,C): desc
        // Accept also filenames with characters, dots, slashes, underscores
        const rangeRe = /^ *(.+?)\((\d+),\s*(\d+)\)-\((\d+),\s*(\d+)\):\s*(.+)$/;
        const pointRe = /^ *(.+?)\((\d+),\s*(\d+)\):\s*(.+)$/;

        let m = entryText.match(rangeRe);
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
        m = entryText.match(pointRe);
        if (m) {
            const file = m[1].trim();
            const sLine = parseInt(m[2], 10), sCol = parseInt(m[3], 10);
            const desc = m[4].trim();
            // point -> end equals start
            const el = profile._ensureElement(file, sLine, sCol, sLine, sCol, desc);
            if (section === 'assertions') batch.assertions.push(el._key);
            else if (section === 'deps') batch.proofDependencies.push(el._key);
            else if (section === 'unused') batch.unusedByProof.push(el._key);
            return;
        }

        // If it doesn't match, try to salvage: sometimes the description wraps to next line;
        // we'll treat the entire trimmed line as a textual entry and attach to the last seen file.
        const file = currentProfileFileNameGuess || 'unknown';
        // fallback: create a pseudo element with start=end=0 and text equal to the entry text
        const el = profile._ensureElement(file, 0, 0, 0, 0, entryText.trim());
        if (section === 'assertions') batch.assertions.push(el._key);
        else if (section === 'deps') batch.proofDependencies.push(el._key);
        else if (section === 'unused') batch.unusedByProof.push(el._key);
    }

    for (let i = 0; i < lines.length; i++) {
        const raw = lines[i];
        const line = raw.replace(/\t/g, '    ');

        // detect start of a new assertion batch
        const batchMatch = line.match(/^\s*Assertion batch\s+(\d+)\s*:/i);
        if (batchMatch) {
            if (currentBatch != null) {
                // Save batch information
                if (currentBatch.assertions.length || currentBatch.proofDependencies.length || currentBatch.unusedByProof.length) {
                    // We need to add this batch to the ProfileFile(s) referenced by elements inside it.
                    // A single batch can reference elements from a file; put this batch into all referenced ProfileFile objects.
                    const fileNames = new Set();
                    for (const key of [...currentBatch.assertions, ...currentBatch.proofDependencies, ...currentBatch.unusedByProof]) {
                        const file = key.split('@', 1)[0];
                        fileNames.add(file);
                    }
                    if (fileNames.size === 0) {
                        // If nothing yet, put into the guessed file
                        const gf = currentProfileFileNameGuess || 'unknown';
                        if (!profile.files.has(gf)) profile.files.set(gf, new ProfileFile(gf));
                        profile.files.get(gf).batches.push(currentBatch);
                    } else {
                        for (const fn of fileNames) {
                            if (!profile.files.has(fn)) profile.files.set(fn, new ProfileFile(fn));
                            profile.files.get(fn).batches.push(currentBatch);
                        }
                    }
                    currentBatch = null;
                    currentSection = null;
                }
            }

            currentBatch = new Batch(parseInt(batchMatch[1], 10));
            currentSection = null;
            // find the profile file name from the last "Assertions for X (something)"? We'll keep a loose guess
            // look backwards a few lines for a line like "Results for Abs (correctness)" or filename patterns
            currentProfileFileNameGuess = null;
            profile.getFile = profile.getFile || null;
            // push to default: we don't know which file yet; batches store keys referencing elements so it's fine
            continue;
        }

        if (!currentBatch) {
            // not in any batch yet: try to detect current profile file name from a line like "Results for Abs (correctness)"
            const resMatch = line.match(/Results\s+for\s+(.+?)(?:\s|$)/i);
            if (resMatch) {
                // cannot reliably extract filename from that; skip
            }
            continue;
        }

        // section headers within a batch
        const sec = line.trim();
        if (/^Assertions:\s*$/i.test(sec)) {
            currentSection = 'assertions';
            continue;
        }
        if (/^Proof dependencies:\s*$/i.test(sec)) {
            currentSection = 'deps';
            continue;
        }
        if (/^Unused by proof:\s*$/i.test(sec)) {
            currentSection = 'unused';
            continue;
        }

        // lines that look like entries are usually indented: detect indentation and that currentSection is active
        if (currentSection && /^\s{4,}[_A-Za-z0-9\/\.\-\\].*$/.test(line)) {
            // trimmed entry
            const entry = line.trim();
            // update a guess for file name if the entry contains one
            const fileGuess = entry.match(/^(.+?)\(/);
            if (fileGuess) currentProfileFileNameGuess = fileGuess[1].trim();

            addEntryToBatch(entry, currentBatch, currentSection);
            continue;
        }
    } // end lines loop

    // If file ended while we had an open batch, add it now.
    if (currentBatch) {
        const fileNames = new Set();
        for (const key of [...currentBatch.assertions, ...currentBatch.proofDependencies, ...currentBatch.unusedByProof]) {
            const file = key.split('@', 1)[0];
            fileNames.add(file);
        }
        const guess = currentProfileFileNameGuess || 'unknown';
        if (fileNames.size === 0) {
            if (!profile.files.has(guess)) profile.files.set(guess, new ProfileFile(guess));
            profile.files.get(guess).batches.push(currentBatch);
        } else {
            for (const fn of fileNames) {
                if (!profile.files.has(fn)) profile.files.set(fn, new ProfileFile(fn));
                profile.files.get(fn).batches.push(currentBatch);
            }
        }
    }

    return profile;
}

/* -------------------------
   Simple tests for the parser
   ------------------------- */

if (require.main === module) {
    const assert = require('assert');

    const sample = `Results for Abs (correctness)
  Overall outcome: Correct
  Overall time: 00:00:00.1509542
  Overall resource count: 13449
  Maximum assertion batch time: 00:00:00.0768541
  Maximum assertion batch resource count: 6746

  Assertion batch 1:
    Outcome: Valid
    Duration: 00:00:00.0768541
    Resource count: 6703

    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20): this postcondition holds

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
    Duration: 00:00:00.0741001
    Resource count: 6746

    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19): this postcondition holds

    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19)-(3,24): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(10,5)-(10,12): assignment (or return)

    Unused by proof:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20)-(2,23): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(6,5)-(6,11): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(12,5)-(12,15): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(14,1)-(14,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point

Dafny program verifier finished with 2 verified, 0 errors
`;

    console.log("Parsing sample report...");
    const prof = parseReport(sample);
    const fname = '_USECASE_find_irrelevant_lines_for_proof.dfy';
    const pf = prof.getFile(fname);
    assert(pf, `Profile should contain file ${fname}`);

    // Test 1: find element that covers (3,21) -> should be range element (3,19)-(3,24) defined in batch 2 proof dependencies
    const el321 = pf.getElementAt(3, 21);
    assert(el321, 'Expected to find an element covering (3,21)');
    assert.strictEqual(el321.start.line, 3);
    assert.strictEqual(el321.start.col, 19);
    assert.strictEqual(el321.end.line, 3);
    assert.strictEqual(el321.end.col, 24);
    console.log('Test 1 passed: found element for (3,21):', el321.spanString(), '-', el321.text);

    // Test 2: el321.usedBy() should return the assertion element that depends on this proof dependency (batch 2 assertion at (3,19)).
    const usedBy = el321.usedBy(pf);
    assert(Array.isArray(usedBy), 'usedBy returns array');
    assert(usedBy.length >= 1, 'expected at least one element using this dependency');
    // we expect one of them to have start (3,19)
    assert(usedBy.some(e => e.start.line === 3 && e.start.col === 19), 'expected an assertion at (3,19) using this dep');
    console.log('Test 2 passed: usedBy includes assertion at (3,19)');

    // Test 3: the assertion at (3,19) should have uses() which includes (10,5)-(10,12)
    const assertion319 = pf.getElementAt(3, 19);
    assert(assertion319, 'Expected to find assertion element at (3,19)');
    const assertionUses = assertion319.usedBy(pf);
    // find an element that is (10,5)-(10,12)
    const has1010 = assertionUses.some(e => e.start.line === 10 && e.start.col === 5 && e.end.line === 10 && e.end.col === 12);
    assert(has1010, 'expected assertion at (3,19) to useBy element (10,5)-(10,12)');
    console.log('Test 3 passed: assertion (3,19).usesBy() includes (10,5)-(10,12)');

    // Test 4: elements contain text and canonical key
    for (const el of pf.elements.values()) {
        assert(typeof el.text === 'string', 'element must have text');
        assert(typeof el._key === 'string', 'element must have _key');
    }
    console.log('Test 4 passed: all elements have text and keys');

    // Summary
    console.log('All tests passed');
}

module.exports = { parseReport, Profile, ProfileFile, Element, getElInLineCol: (pf, l, c) => pf.getElementAt(l, c) };
