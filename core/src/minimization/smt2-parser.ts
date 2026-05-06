/**
 * SMT2 S-expression parser — ported from Python minimize_unsat_core_trace.py
 */

export class SMT2Error extends Error {
  constructor(message: string) {
    super(message);
    this.name = "SMT2Error";
  }
}

export interface Command {
  text: string;
  head: string | null;
  label: string | null;
}

/**
 * Split SMT-LIB text into top-level S-expressions.
 * Handles comments, double-quoted strings with escapes, bar-quoted symbols, nested parens.
 */
export function splitTopLevel(text: string): string[] {
  const items: string[] = [];
  let buf: string[] = [];
  let depth = 0;
  let inComment = false;
  let inString = false;
  let inBar = false;
  let escape = false;

  for (const ch of text) {
    if (inComment) {
      if (ch === "\n") {
        inComment = false;
        if (depth > 0) {
          buf.push(ch);
        }
      }
      continue;
    }

    if (inString) {
      buf.push(ch);
      if (escape) {
        escape = false;
      } else if (ch === "\\") {
        escape = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }

    if (inBar) {
      buf.push(ch);
      if (ch === "|") {
        inBar = false;
      }
      continue;
    }

    if (ch === ";") {
      inComment = true;
      continue;
    }

    if (ch === '"') {
      if (depth > 0) {
        buf.push(ch);
      }
      inString = true;
      continue;
    }

    if (ch === "|") {
      if (depth > 0) {
        buf.push(ch);
      }
      inBar = true;
      continue;
    }

    if (ch === "(") {
      if (depth === 0) {
        buf = [];
      }
      buf.push(ch);
      depth++;
      continue;
    }

    if (ch === ")") {
      if (depth === 0) {
        throw new SMT2Error("Unbalanced parentheses while parsing SMT2 file");
      }
      buf.push(ch);
      depth--;
      if (depth === 0) {
        items.push(buf.join("").trim());
        buf = [];
      }
      continue;
    }

    if (depth > 0) {
      buf.push(ch);
    }
  }

  if (depth !== 0 || inString || inBar) {
    throw new SMT2Error("Incomplete top-level SMT2 expression");
  }

  return items.filter((item) => item.length > 0);
}

/**
 * Extract first head symbol from S-expression: "(assert ...)" → "assert"
 */
export function firstHead(expr: string): string | null {
  const m = expr.match(/^\(\s*([^\s()]+)/s);
  return m ? m[1] : null;
}

/**
 * Extract :named label from assert command.
 */
export function extractNamedLabel(assertCmd: string): string | null {
  if (firstHead(assertCmd) !== "assert") {
    return null;
  }
  const m = assertCmd.match(/:named\s+([^\s()]+)/s);
  return m ? m[1] : null;
}

/**
 * Parse int arg from command like "(push 1)".
 * Throws SMT2Error if form doesn't match.
 */
export function parsePositiveIntCommand(expr: string, expectedHead: string): number {
  const escaped = expectedHead.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`^\\(\\s*${escaped}\\s+(\\d+)\\s*\\)$`);
  const m = expr.trim().match(re);
  if (!m) {
    throw new SMT2Error(`Unsupported command form: ${expr}`);
  }
  return parseInt(m[1], 10);
}

/**
 * Parse commands from file content string.
 */
export function parseCommands(text: string): Command[] {
  const raw = splitTopLevel(text);
  return raw.map((expr) => {
    const head = firstHead(expr);
    const label = extractNamedLabel(expr);
    return { text: expr, head, label };
  });
}

/**
 * Extract first balanced S-expression from text.
 * Returns null if no opening paren found or expression is incomplete.
 */
export function extractFirstBalancedSexpr(text: string): string | null {
  const start = text.indexOf("(");
  if (start === -1) {
    return null;
  }

  let depth = 0;
  let inString = false;
  let inBar = false;
  let escape = false;

  for (let i = start; i < text.length; i++) {
    const ch = text[i];

    if (inString) {
      if (escape) {
        escape = false;
      } else if (ch === "\\") {
        escape = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }

    if (inBar) {
      if (ch === "|") {
        inBar = false;
      }
      continue;
    }

    if (ch === '"') {
      inString = true;
      continue;
    }

    if (ch === "|") {
      inBar = true;
      continue;
    }

    if (ch === "(") {
      depth++;
    } else if (ch === ")") {
      depth--;
      if (depth === 0) {
        return text.slice(start, i + 1);
      }
    }
  }

  return null;
}

/**
 * Parse unsat core S-expression "(label1 label2 ...)" into string[].
 */
export function parseCoreExpr(expr: string): string[] {
  const trimmed = expr.trim();
  if (!trimmed.startsWith("(") || !trimmed.endsWith(")")) {
    throw new SMT2Error(`Malformed unsat core S-expression: ${JSON.stringify(trimmed)}`);
  }
  const inner = trimmed.slice(1, -1).trim();
  if (!inner) {
    return [];
  }
  return inner.split(/\s+/);
}
