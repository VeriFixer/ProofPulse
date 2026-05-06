/**
 * Incremental S-expression reader from a readable stream.
 * Port of Python read_commands() from z3-minimizer-wrapper.py.
 *
 * Reads one byte at a time in paused mode, tracking paren depth,
 * string/bar/comment state to return one complete top-level
 * S-expression or bare token per call. Returns empty string on EOF.
 */

/**
 * Read a single character (byte) from a readable stream in paused mode.
 * Returns null on EOF.
 */
function readChar(stream: NodeJS.ReadableStream): Promise<string | null> {
  return new Promise((resolve) => {
    const chunk = (stream as NodeJS.ReadableStream & { read(size: number): Buffer | null }).read(1);
    if (chunk !== null) {
      resolve(chunk.toString("utf8"));
      return;
    }
    // No data available yet — wait for 'readable' or 'end'
    const onReadable = (): void => {
      cleanup();
      const data = (stream as NodeJS.ReadableStream & { read(size: number): Buffer | null }).read(1);
      if (data !== null) {
        resolve(data.toString("utf8"));
      } else {
        resolve(null);
      }
    };
    const onEnd = (): void => {
      cleanup();
      resolve(null);
    };
    const cleanup = (): void => {
      stream.removeListener("readable", onReadable);
      stream.removeListener("end", onEnd);
    };
    stream.on("readable", onReadable);
    stream.on("end", onEnd);
  });
}

export function createStdinReader(stream: NodeJS.ReadableStream): {
  readCommand(): Promise<string>;
} {
  return {
    async readCommand(): Promise<string> {
      const buf: string[] = [];
      let depth = 0;
      let inString = false;
      let inBar = false;
      let inComment = false;
      let escape = false;
      let started = false;

      while (true) {
        const ch = await readChar(stream);
        if (ch === null) {
          // EOF
          if (started) {
            return buf.join("");
          }
          return "";
        }

        if (inComment) {
          buf.push(ch);
          if (ch === "\n") {
            inComment = false;
            if (!started) {
              // standalone comment, skip
              buf.length = 0;
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
          buf.push(ch);
          inComment = true;
          continue;
        }

        if (ch === '"') {
          buf.push(ch);
          inString = true;
          if (!started) {
            started = true;
          }
          continue;
        }

        if (ch === "|") {
          buf.push(ch);
          inBar = true;
          if (!started) {
            started = true;
          }
          continue;
        }

        if (ch === "(") {
          buf.push(ch);
          depth++;
          started = true;
          continue;
        }

        if (ch === ")") {
          buf.push(ch);
          depth--;
          if (depth <= 0) {
            return buf.join("").trim();
          }
          continue;
        }

        if (depth > 0) {
          buf.push(ch);
          continue;
        }

        // Outside parens — whitespace or bare token
        if (ch === " " || ch === "\t" || ch === "\r" || ch === "\n") {
          if (started && buf.length > 0) {
            return buf.join("").trim();
          }
          continue;
        }

        buf.push(ch);
        started = true;
      }
    },
  };
}
