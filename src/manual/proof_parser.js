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

const CovStatus = {
    CovComplete: 1,
    CovTest: 2,
    Uncovered: 3
};

const TokenType = {
    Other : 0,
    Precondition : 1,
    Postcondition : 2,
    Assertion : 3,
    CodeLine : 4
}

class prooftoken {
    constructor(file, sLine, sCol, eLine, eCol, prooftext, isTopAssertion) {
        this.file = file;
        this.prooftext = prooftext;
        this.start = { line: sLine, col: sCol };
        this.end = { line: eLine, col: eCol };
        this.isTopAssertion = isTopAssertion;
        
        this.CovStatus = CovStatus.Uncovered;
        this.tokenType = TokenType.Other;

        // Code only for top levelTokens 
        if(isTopAssertion){
          this.proofUsedTokens = [];
          this.proofUnusedTokens = [];
          if("postcondition" in prooftext){
            this.type = TokenType.Postcondition;
          } // TO COMPLETE
        }
    }
}

class proof {
    constructor(proofLog){
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

    }

}