const dollar = s => document.querySelector(s);
const dollarAll = s => Array.from(document.querySelectorAll(s));

const pre = dollar('#source');
const panelBody = dollar('#panel-body');
const panelTitle = dollar('#panel-title');

function escapeHtml(s) {
    return String(s)
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
}

function buildSourceDomFromFragment(fragmentHtml, code, lineStatuses) {
    const linesHtml = fragmentHtml.split('\n');
    const linesText = code.split('\n');
    const container = document.createDocumentFragment();

    for (let i = 0; i < Math.max(linesHtml.length, linesText.length); i++) {
        const lineNum = i + 1;
        const status = (lineStatuses[i]) ? lineStatuses[i] : CovStatus.CovComplete;
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
    dollarAll('.token').forEach(t => t.classList.remove('selected', 'related'));
}

function renderPanel(tokenEl, proof) {
    const id = tokenEl.dataset.id;

    const token =  proof.proofGraph.getNode(id);

    panelTitle.textContent = `Dependency tracker: ${tokenEl.textContent.trim()}`;
    

    let DepensOn = window.getDependsOn(id, proof, 1);
    let DepensOnIds = DepensOn.map(obj => obj.id);

    clearHighlights();

    tokenEl.classList.add('selected');
    DepensOnIds.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });

    panelBody.innerHTML = '';

    panelBody.insertAdjacentHTML('beforeend', `
    <p><strong>Status:</strong> ${String(token.CovStatus)}</p>
    <p><strong>Message:</strong> ${String(token.prooftext)}</p>
    <p><strong>Loc:</strong> ${String(id)}</p>
    <p><strong>Kind:</strong> ${String(token.type)}</p>
    <p><strong>CovInternal:</strong> ${String(token.CovStatusInternal)}</p>
    `);

    const usedByDiv = document.createElement('div'); usedByDiv.className = 'group';
    usedByDiv.innerHTML = `<strong>All Related (${DepensOnIds.length}):</strong>`;
    const usedByList = document.createElement('ul');
    DepensOnIds.forEach(uid => {
        const tokenbase =  proof.proofGraph.getNode(uid);
        const el = document.querySelector(`[data-id="${uid}"]`);
        const li = document.createElement('li');
        li.textContent = el ? `${el.textContent.trim()} (id=${uid}) (${tokenbase.prooftext})` : uid;
        usedByList.appendChild(li);
    });
    usedByDiv.appendChild(usedByList);
    panelBody.appendChild(usedByDiv);
    const graphDiv = document.createElement('div'); graphDiv.className = 'group';
  }

function attachHandlers(proof) {
  // Make tokens focusable so keyboard navigation still works:
  dollarAll('.token').forEach(t => t.tabIndex = 0);

  // Click delegation: choose the deepest .token
  pre.addEventListener('click', e => {
    const tokenEl = e.target.closest('.token');
    if (!tokenEl) return;
    renderPanel(tokenEl, proof);
  });

  // Keyboard: keep per-token keydown so focus + Enter/Space works reliably
  dollarAll('.token').forEach(t => {
    t.addEventListener('keydown', e => {
      if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        renderPanel(e.currentTarget, proof);
      }
    });
  });
}

let currentProof = null;
let selectedTest = null;

function clearState() {
    pre.innerHTML = '';
    panelBody.innerHTML = '';
    panelTitle.textContent = 'Select a token';
    currentProof = null;
}

async function loadTestList() {
    const resp = await fetch('/api/tests');
    const tests = await resp.json();
    const list = dollar('#test-list');
    list.innerHTML = '';
    tests.forEach(name => {
        const entry = document.createElement('div');
        entry.className = 'test-entry';
        entry.textContent = name;
        entry.addEventListener('click', () => loadTest(name));
        list.appendChild(entry);
    });
}

async function loadTest(name) {
    clearState();
    dollar('#editor-title').textContent = name;

    const [source, log] = await Promise.all([
        fetch(`/api/tests/${encodeURIComponent(name)}/source`).then(r => r.text()),
        fetch(`/api/tests/${encodeURIComponent(name)}/log`).then(r => r.text()),
    ]);

    currentProof = window.parseProof(source, log);
    const lineStatuses = currentProof.lineStatus;
    const src = window.getSourceCode();
    const fragment = window.generateSpansFragment(src, currentProof);
    buildSourceDomFromFragment(fragment, src, lineStatuses);
    attachHandlers(currentProof);

    dollarAll('.test-entry').forEach(el => el.classList.remove('active'));
    const match = dollarAll('.test-entry').find(el => el.textContent === name);
    if (match) match.classList.add('active');
    selectedTest = name;

    const uncovered = document.querySelector('.token[data-status="uncovered"]');
    if (uncovered) renderPanel(uncovered, currentProof);
    else {
        const first = document.querySelector('.token');
        if (first) renderPanel(first, currentProof);
    }
}

function switchToBrowser() {
    dollar('#test-list').style.display = '';
    dollar('#interactive-panel').style.display = 'none';
    dollar('#btn-browser').classList.add('active');
    dollar('#btn-interactive').classList.remove('active');
    dollar('#btn-browser').setAttribute('aria-pressed', 'true');
    dollar('#btn-interactive').setAttribute('aria-pressed', 'false');
}

function switchToInteractive() {
    dollar('#test-list').style.display = 'none';
    dollar('#interactive-panel').style.display = '';
    dollar('#btn-interactive').classList.add('active');
    dollar('#btn-browser').classList.remove('active');
    dollar('#btn-interactive').setAttribute('aria-pressed', 'true');
    dollar('#btn-browser').setAttribute('aria-pressed', 'false');
}

async function runInteractive(code) {
    const loadingEl = dollar('#loading-indicator');
    const btnRun = dollar('#btn-run');
    loadingEl.style.display = '';
    btnRun.disabled = true;

    try {
        const resp = await fetch('/api/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ code }),
        });
        const data = await resp.json();

        if (data.error) {
            clearState();
            pre.textContent = data.error + (data.stderr ? '\n' + data.stderr : '');
            return;
        }

        clearState();
        dollar('#editor-title').textContent = 'Interactive run';
        currentProof = window.parseProof(code, data.log);
        const lineStatuses = currentProof.lineStatus;
        const src = window.getSourceCode();
        const fragment = window.generateSpansFragment(src, currentProof);
        buildSourceDomFromFragment(fragment, src, lineStatuses);
        attachHandlers(currentProof);

        const uncovered = document.querySelector('.token[data-status="uncovered"]');
        if (uncovered) renderPanel(uncovered, currentProof);
        else {
            const first = document.querySelector('.token');
            if (first) renderPanel(first, currentProof);
        }
    } catch (err) {
        clearState();
        pre.textContent = 'Request failed: ' + err.message;
    } finally {
        loadingEl.style.display = 'none';
        btnRun.disabled = false;
    }
}

async function bootstrap() {
    // Wire mode toggle handlers
    dollar('#btn-browser').addEventListener('click', switchToBrowser);
    dollar('#btn-interactive').addEventListener('click', switchToInteractive);

    // Wire run button
    dollar('#btn-run').addEventListener('click', () => {
        const code = dollar('#code-input').value;
        if (code.trim()) runInteractive(code);
    });

    // Default to browser mode
    switchToBrowser();

    // Load test list
    try {
        await loadTestList();
    } catch (e) {
        pre.textContent = 'Failed to load test list: ' + e.message;
    }
}

bootstrap();
