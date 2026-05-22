#!/usr/bin/env bash
# Invokes kiro-cli headless for each divergence to classify root causes.
# Uses pre-built prompts from divergence-prompts.json (with coverage annotations).
#
# Usage:
#   ./evaluation/run-classify-divergences.sh [--concurrency N] [--model MODEL]
#
# Requires: KIRO_API_KEY env var, kiro-cli on PATH
# Output:   evaluation/results/agent-classifications.json

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PROMPTS_FILE="$REPO_ROOT/evaluation/results/divergence-prompts.json"
OUTPUT="$REPO_ROOT/evaluation/results/agent-classifications.json"
AGENT_DIR="$REPO_ROOT/evaluation/agents"
TMP_DIR="$REPO_ROOT/.eval-tmp/classify-runs"

# Defaults
CONCURRENCY=4
MODEL="qwen3-coder-next"

# Parse flags
while [[ $# -gt 0 ]]; do
  case $1 in
    --concurrency) CONCURRENCY="$2"; shift 2 ;;
    --model) MODEL="$2"; shift 2 ;;
    *) echo "Unknown flag: $1"; exit 1 ;;
  esac
done

# Validate
if [ ! -f "$PROMPTS_FILE" ]; then
  echo "ERROR: $PROMPTS_FILE not found. Run the benchmark first."
  exit 1
fi

if ! command -v kiro-cli &>/dev/null; then
  echo "ERROR: kiro-cli not found on PATH"
  exit 1
fi

if [ -z "${KIRO_API_KEY:-}" ]; then
  echo "ERROR: KIRO_API_KEY not set. Headless mode requires an API key."
  echo "Generate one at https://app.kiro.dev/ under Settings > API Keys"
  exit 1
fi

mkdir -p "$TMP_DIR"

# Update agent config model
node --input-type=module -e "
import fs from 'node:fs';
const cfg = JSON.parse(fs.readFileSync('$AGENT_DIR/classify-divergence.json','utf8'));
cfg.model = '$MODEL';
fs.writeFileSync('$AGENT_DIR/classify-divergence.json', JSON.stringify(cfg, null, 2) + '\n');
"

# Generate per-divergence prompt files (system + user + log combined)
TOTAL=$(node --input-type=module -e "
import fs from 'node:fs';
import path from 'node:path';

const prompts = JSON.parse(fs.readFileSync('$PROMPTS_FILE', 'utf8'));
const tmpDir = '$TMP_DIR';
const repoRoot = '$REPO_ROOT';

for (let i = 0; i < prompts.length; i++) {
  const p = prompts[i];

  // Read ProofPulse log if it exists
  let logContent = '';
  const logPath = path.join(repoRoot, '.eval-tmp/logs', p.dataset, 'task_id_' + p.taskId + '.log.txt');
  if (fs.existsSync(logPath)) {
    logContent = '\n\nProofPulse CLI log:\n\`\`\`\n' + fs.readFileSync(logPath, 'utf8').slice(0, 2000) + '\n\`\`\`';
  }

  // Combine: system prompt + user prompt + log
  const combined = p.systemPrompt + '\n\n---\n\n' + p.userPrompt + logContent;
  fs.writeFileSync(path.join(tmpDir, 'prompt_' + i + '.txt'), combined);
}

console.log(prompts.length);
")

echo "Classifying $TOTAL divergences with model=$MODEL, concurrency=$CONCURRENCY"
echo "Agent config: $AGENT_DIR/classify-divergence.json"
echo "Prompts source: $PROMPTS_FILE"
echo ""
echo "Starting classifications..."

# Classification function
classify_one() {
  local idx=$1
  local prompt_file="$TMP_DIR/prompt_${idx}.txt"
  local out_file="$TMP_DIR/result_${idx}.json"

  local prompt
  prompt=$(cat "$prompt_file")

  # Call kiro-cli headless with no tools
  local response
  response=$(kiro-cli chat --no-interactive --agent "$AGENT_DIR/classify-divergence.json" "$prompt" 2>/dev/null) || response=""

  # Extract JSON from response
  echo "$response" | node --input-type=module -e "
    import fs from 'node:fs';
    let input = '';
    process.stdin.on('data', d => input += d);
    process.stdin.on('end', () => {
      const match = input.match(/\{[^}]*rootCause[^}]*\}/s);
      if (match) {
        try {
          const obj = JSON.parse(match[0]);
          fs.writeFileSync('$out_file', JSON.stringify(obj));
          process.exit(0);
        } catch(e) {}
      }
      fs.writeFileSync('$out_file', JSON.stringify({rootCause:'other',explanation:'Failed to parse agent response',confidence:0.0,oracleError:false}));
      process.exit(0);
    });
  " || true
}

export -f classify_one
export TMP_DIR AGENT_DIR TOTAL

# Run with concurrency using background jobs + wait -n
RUNNING=0
DONE=0

for i in $(seq 0 $((TOTAL - 1))); do
  classify_one "$i" &
  RUNNING=$((RUNNING + 1))

  if [ "$RUNNING" -ge "$CONCURRENCY" ]; then
    wait -n 2>/dev/null || true
    DONE=$((DONE + 1))
    echo "[$DONE/$TOTAL] classified"
    RUNNING=$((RUNNING - 1))
  fi
done

# Wait for remaining
while [ "$DONE" -lt "$TOTAL" ]; do
  wait -n 2>/dev/null || true
  DONE=$((DONE + 1))
  echo "[$DONE/$TOTAL] classified"
done

echo ""
echo "Assembling results..."

# Assemble final JSON
node --input-type=module -e "
import fs from 'node:fs';
import path from 'node:path';

const prompts = JSON.parse(fs.readFileSync('$PROMPTS_FILE', 'utf8'));
const tmpDir = '$TMP_DIR';
const repoRoot = '$REPO_ROOT';
const classifications = [];

for (let i = 0; i < prompts.length; i++) {
  const p = prompts[i];
  const resultFile = path.join(tmpDir, 'result_' + i + '.json');

  let result = { rootCause: 'other', explanation: 'No result file', confidence: 0.0, oracleError: false };
  if (fs.existsSync(resultFile)) {
    try {
      result = JSON.parse(fs.readFileSync(resultFile, 'utf8'));
    } catch(e) {}
  }

  // Find log path
  const logPath = '.eval-tmp/logs/' + p.dataset + '/task_id_' + p.taskId + '.log.txt';
  const logExists = fs.existsSync(path.join(repoRoot, logPath));

  classifications.push({
    dataset: p.dataset,
    taskId: p.taskId,
    category: p.category,
    direction: p.direction,
    predicted: p.predicted,
    oracle: p.oracle,
    rootCause: result.rootCause,
    explanation: result.explanation || '',
    confidence: result.confidence ?? 0.5,
    oracleError: result.oracleError || false,
    relativePath: p.relativePath,
    logPath: logExists ? logPath : null
  });
}

fs.writeFileSync('$OUTPUT', JSON.stringify({ classifications, metadata: { model: '$MODEL', date: new Date().toISOString(), total: classifications.length } }, null, 2));

// Summary
const counts = {};
for (const c of classifications) {
  counts[c.rootCause] = (counts[c.rootCause] || 0) + 1;
}

console.log('Written ' + classifications.length + ' classifications to:');
console.log('  $OUTPUT');
console.log('');
console.log('Root cause summary:');
Object.entries(counts)
  .sort((a,b) => b[1] - a[1])
  .forEach(([k,v]) => console.log('  ' + k.padEnd(30) + v));
"

echo ""
echo "Done. Now run: npx tsx evaluation/generate-results-after-analysis-md.ts"
