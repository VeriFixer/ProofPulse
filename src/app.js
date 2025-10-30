const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));

const pre = $('#source');
const panelBody = $('#panel-body');
const panelTitle = $('#panel-title');

function escapeHtml(s) {
    return String(s)
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
}

function computeLineStatusesFromTokens(code, tokens) {
    const lines = code.split('\n');
    const statusByLine = new Array(lines.length).fill('covered-complete');
    if (!tokens || tokens.length === 0) return statusByLine;
    const mapStatus = (s) => {
        if (s === window.CovStatus.Uncovered || s === 3 || String(s).toLowerCase().includes('uncover')) return 'uncovered';
        if (s === window.CovStatus.CovTest || s === 2 || String(s).toLowerCase().includes('test')) return 'covered-test';
        return 'covered-complete';
    };
    for (const t of tokens) {
        if (!t || !t.start || !t.end) continue;
        const sLine = Math.max(1, t.start.line || 1);
        const eLine = Math.max(sLine, t.end.line || sLine);
        const mapped = mapStatus(t.CovStatus);
        for (let ln = sLine; ln <= eLine; ln++) {
            const idx = ln - 1;
            if (statusByLine[idx] === 'uncovered') continue;
            if (mapped === 'uncovered') statusByLine[idx] = 'uncovered';
            else if (mapped === 'covered-test' && statusByLine[idx] !== 'uncovered') statusByLine[idx] = 'covered-test';
        }
    }
    return statusByLine;
}

function buildSourceDomFromFragment(fragmentHtml, code, lineStatuses) {
    const linesHtml = fragmentHtml.split('\n');
    const linesText = code.split('\n');
    const container = document.createDocumentFragment();

    for (let i = 0; i < Math.max(linesHtml.length, linesText.length); i++) {
        const lineNum = i + 1;
        const status = (lineStatuses && lineStatuses[i]) ? lineStatuses[i] : 'covered-complete';
        const div = document.createElement('div');
        div.className = 'line';
        div.dataset.line = String(lineNum);
        div.dataset.status = status;

        const lnum = document.createElement('span');
        lnum.className = 'lnum';
        lnum.textContent = String(lineNum).padStart(4, '0');
        div.appendChild(lnum);

        const contentHtml = linesHtml[i] !== undefined
            ? linesHtml[i]
            : escapeHtml(linesText[i] || '');

        const wrapper = document.createElement('span');
        wrapper.innerHTML = contentHtml;
        div.appendChild(wrapper);

        container.appendChild(div);
    }

    pre.innerHTML = '';
    pre.appendChild(container);
}

function clearHighlights() {
    $$('.token').forEach(t => t.classList.remove('selected', 'related'));
}

function renderPanel(tokenEl, deps) {
    const id = tokenEl.dataset.id;
    panelTitle.textContent = `Dependency tracker — ${tokenEl.textContent.trim()}`;

    let usedOnIds = window.getUsedOn(id, deps);
    let DepensOnIds = window.getDependsOn(id, deps);

    clearHighlights();

    tokenEl.classList.add('selected');
    usedOnIds.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });
    DepensOnIds.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });

    panelBody.innerHTML = '';

    const status = tokenEl.dataset.status || 'unknown';
    const statusP = document.createElement('p');
    statusP.innerHTML = `<strong>Status:</strong> ${status}`;
    panelBody.appendChild(statusP);


    const usesDiv = document.createElement('div'); usesDiv.className = 'group';
    usesDiv.innerHTML = `<strong> Later Proof Dependency (${usedOnIds.length}):</strong>`;
    const usesList = document.createElement('ul');
    usedOnIds.forEach(uid => {
        const el = document.querySelector(`[data-id="${uid}"]`);
        const li = document.createElement('li');
        li.textContent = el ? `${el.textContent.trim()} (id=${uid})` : uid;
        usesList.appendChild(li);
    });
    usesDiv.appendChild(usesList);
    panelBody.appendChild(usesDiv);



    const usedByDiv = document.createElement('div'); usedByDiv.className = 'group';
    usedByDiv.innerHTML = `<strong>Earlier Proof Dependency (${DepensOnIds.length}):</strong>`;
    const usedByList = document.createElement('ul');
    DepensOnIds.forEach(uid => {
        const el = document.querySelector(`[data-id="${uid}"]`);
        const li = document.createElement('li');
        li.textContent = el ? `${el.textContent.trim()} (id=${uid})` : uid;
        usedByList.appendChild(li);
    });
    usedByDiv.appendChild(usedByList);
    panelBody.appendChild(usedByDiv);

    const graphDiv = document.createElement('div'); graphDiv.className = 'group';
    graphDiv.innerHTML = `<strong>Local proof view</strong>`;
    const node = document.createElement('div'); node.className = 'graph-node';
    node.innerHTML = `<div class="title">${tokenEl.textContent.trim()} <span style="font-size:12px;color:var(--muted)">(${id})</span></div>` +
        `<div class="meta">uses: ${usedOnIds.join(', ') || '—'} • usedBy: ${DepensOnIds.join(', ') || '—'}</div>`;
    graphDiv.appendChild(node);
    panelBody.appendChild(graphDiv);
}

function attachHandlers(deps) {
    $$('.token').forEach(t => {
        t.addEventListener('click', e => { renderPanel(t, deps); });
        t.tabIndex = 0;
        t.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); renderPanel(t, deps); } });
    });
}

async function bootstrap() {
    const proofFile = "prover_log.txt";
    const sourceFile = "source_code.dfy";

    // Fetch file contents first
    const [dafnyCode, proofLog] = await Promise.all([
        fetch(sourceFile).then(r => r.text()),
        fetch(proofFile).then(r => r.text())
    ]);

    // Then pass the actual content strings to parseProof
    let proof = root.parseProof(dafnyCode, proofLog);
    window.proofObj = proof;
    const src = window.getSourceCode();

    console.log("Loaded Dafny source code:\n", src);

    let tokens = window.proofObj.allTokens;

    const fragment = window.generateSpansFragment(src, tokens);
    const lineStatuses = computeLineStatusesFromTokens(src, tokens);
    buildSourceDomFromFragment(fragment, src, lineStatuses);

    const deps = window.proofObj;
    attachHandlers(deps);

    const uncovered = document.querySelector('.token[data-status="uncovered"]');
    if (uncovered) renderPanel(uncovered, deps);
    else {
        const first = document.querySelector('.token');
        if (first) renderPanel(first, deps);
    }

}

bootstrap();
