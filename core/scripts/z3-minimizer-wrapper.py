#!/usr/bin/env python3
"""
Interactive z3 wrapper that acts as a drop-in z3 replacement for Boogie.

Boogie communicates with z3 via stdin/stdout pipe using `-smt2 -in` mode.
This wrapper proxies all commands to real z3, but intercepts check-sat /
get-unsat-core sequences to perform unsat-core minimization.

Three binaries involved:
  1. dafny  — spawns Boogie which spawns this wrapper
  2. this wrapper — pretends to be z3, proxies to real z3
  3. real z3 — the actual solver (PROOFPULSE_Z3_PATH)
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import List, Optional, Sequence

# ---------------------------------------------------------------------------
# Import minimizer helpers — lives next to this script
# ---------------------------------------------------------------------------
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from minimize_unsat_core_trace import (
    Command,
    SMT2Error,
    build_script,
    extract_named_label,
    first_head,
    minimize_core_for_block,
    parse_core_from_marked_output,
    parse_positive_int_command,
    parse_status,
    run_z3,
)

# ---------------------------------------------------------------------------
# Config from environment
# ---------------------------------------------------------------------------
Z3_PATH = os.environ.get("PROOFPULSE_Z3_PATH", "z3")
LOG_FILE = os.environ.get("PROOFPULSE_WRAPPER_LOG", "")

QUERY_COMMANDS = {
    "check-sat", "check-sat-assuming",
    "get-unsat-core", "get-model", "get-assignment",
    "get-value", "get-proof", "get-info", "echo",
}


def log(msg: str) -> None:
    if LOG_FILE:
        with open(LOG_FILE, "a") as f:
            f.write(msg + "\n")


# ---------------------------------------------------------------------------
# Incremental S-expression reader from stdin
# ---------------------------------------------------------------------------
def read_commands(stream) -> str:
    """Read one complete top-level S-expression or bare token from stream."""
    buf: List[str] = []
    depth = 0
    in_string = False
    in_bar = False
    in_comment = False
    escape = False
    started = False

    while True:
        ch = stream.read(1)
        if not ch:
            # EOF
            if started:
                return "".join(buf)
            return ""

        if in_comment:
            buf.append(ch)
            if ch == "\n":
                in_comment = False
                if not started:
                    # standalone comment, skip
                    buf = []
            continue

        if in_string:
            buf.append(ch)
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue

        if in_bar:
            buf.append(ch)
            if ch == "|":
                in_bar = False
            continue

        if ch == ";":
            buf.append(ch)
            in_comment = True
            continue

        if ch == '"':
            buf.append(ch)
            in_string = True
            if not started:
                started = True
            continue

        if ch == "|":
            buf.append(ch)
            in_bar = True
            if not started:
                started = True
            continue

        if ch == "(":
            buf.append(ch)
            depth += 1
            started = True
            continue

        if ch == ")":
            buf.append(ch)
            depth -= 1
            if depth <= 0:
                return "".join(buf).strip()
            continue

        if depth > 0:
            buf.append(ch)
            continue

        # Outside parens — whitespace or bare token
        if ch in (" ", "\t", "\r", "\n"):
            if started and buf:
                return "".join(buf).strip()
            continue

        buf.append(ch)
        started = True


def make_cmd(text: str) -> Command:
    head = first_head(text)
    label = extract_named_label(text) if head == "assert" else None
    return Command(text=text, head=head, label=label)


# ---------------------------------------------------------------------------
# Forward a single command to real z3 and return its output
# ---------------------------------------------------------------------------
def forward_to_z3(z3_proc: subprocess.Popen, cmd_text: str) -> str:
    """Send a command to the running z3 process and read its response."""
    z3_proc.stdin.write(cmd_text + "\n")
    z3_proc.stdin.flush()
    # We need to know how many response lines to expect.
    # Use an echo sentinel to know when z3 is done.
    sentinel = "__PP_SENTINEL__"
    z3_proc.stdin.write(f'(echo "{sentinel}")\n')
    z3_proc.stdin.flush()

    lines: List[str] = []
    while True:
        line = z3_proc.stdout.readline()
        if not line:
            break
        line = line.rstrip("\n")
        if sentinel in line:
            break
        lines.append(line)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main interactive loop
# ---------------------------------------------------------------------------
def main() -> int:
    # Handle -version: Boogie calls this first
    if "-version" in sys.argv:
        proc = subprocess.run([Z3_PATH, "-version"], capture_output=True, text=True)
        sys.stdout.write(proc.stdout)
        sys.stdout.flush()
        return proc.returncode

    log(f"wrapper started, z3={Z3_PATH}, args={sys.argv[1:]}")

    # Start real z3 for the live proxy session
    z3_args = [Z3_PATH] + [a for a in sys.argv[1:] if a not in ("-smt2", "-in")]
    z3_args.extend(["-smt2", "-in"])
    z3_proc = subprocess.Popen(
        z3_args,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    # Track solver state for minimization
    frames: List[List[Command]] = [[]]
    stdin = sys.stdin
    stdout = sys.stdout

    def emit(text: str) -> None:
        stdout.write(text + "\n")
        stdout.flush()

    def current_context() -> List[Command]:
        out: List[Command] = []
        for frame in frames:
            out.extend(frame)
        return out

    try:
        while True:
            raw = read_commands(stdin)
            if not raw:
                break

            cmd = make_cmd(raw)
            head = cmd.head
            log(f"cmd: {head} | {raw[:80]}")

            # --- State tracking ---
            if head == "push":
                count = parse_positive_int_command(cmd.text, "push")
                for _ in range(count):
                    frames.append([])
                resp = forward_to_z3(z3_proc, raw)
                if resp:
                    emit(resp)
                continue

            if head == "pop":
                count = parse_positive_int_command(cmd.text, "pop")
                for _ in range(count):
                    if len(frames) > 1:
                        frames.pop()
                resp = forward_to_z3(z3_proc, raw)
                if resp:
                    emit(resp)
                continue

            if head == "reset":
                frames = [[]]
                resp = forward_to_z3(z3_proc, raw)
                if resp:
                    emit(resp)
                continue

            # --- Query block: check-sat possibly followed by get-unsat-core ---
            if head in ("check-sat", "check-sat-assuming"):
                # Forward check-sat to live z3
                status_resp = forward_to_z3(z3_proc, raw)
                log(f"check-sat response: {status_resp}")

                status = status_resp.strip()

                # Peek ahead: is next command get-unsat-core?
                # We need to read it to know, but we can't un-read.
                # Instead, always forward and only minimize if unsat + get-unsat-core.
                #
                # For now: emit the status. If next cmd is get-unsat-core and
                # status was unsat, we'll minimize at that point.
                emit(status_resp)

                # Store status for potential get-unsat-core that follows
                last_check_sat_status = status
                last_check_sat_cmd = cmd
                continue

            if head == "get-unsat-core":
                # Get the core from live z3
                core_resp = forward_to_z3(z3_proc, raw)
                log(f"get-unsat-core response: {core_resp[:200]}")

                # Try to minimize
                try:
                    ctx = current_context()
                    query_block = [
                        last_check_sat_cmd,
                        cmd,
                    ]
                    # Parse the core from z3's response
                    core_text = core_resp.strip()
                    if core_text.startswith("("):
                        inner = core_text[1:-1].strip()
                        initial_core = inner.split() if inner else []
                    else:
                        initial_core = []

                    if initial_core:
                        minimized = minimize_core_for_block(
                            Z3_PATH, ctx, query_block, initial_core
                        )
                        emit("(" + " ".join(minimized) + ")")
                        log(f"minimized core: {len(initial_core)} -> {len(minimized)}")
                    else:
                        emit(core_resp)
                except Exception as e:
                    log(f"minimization failed, passing through: {e}")
                    emit(core_resp)
                continue

            # --- Other query commands: forward transparently ---
            if head in QUERY_COMMANDS:
                resp = forward_to_z3(z3_proc, raw)
                emit(resp)
                continue

            # --- Non-query command (assert, declare, define, set-option, etc.) ---
            if cmd.label is not None or head == "assert":
                frames[-1].append(cmd)
            elif head in ("declare-fun", "declare-sort", "declare-const",
                          "declare-datatypes", "define-fun", "define-sort",
                          "set-option", "set-info", "set-logic"):
                frames[-1].append(cmd)

            resp = forward_to_z3(z3_proc, raw)
            if resp:
                emit(resp)

    except Exception as e:
        log(f"wrapper error: {e}")
        # On error, try to pass through remaining stdin/stdout
        import traceback
        log(traceback.format_exc())
    finally:
        try:
            z3_proc.stdin.close()
        except Exception:
            pass
        z3_proc.wait()
        log("wrapper done")

    return 0


# Track last check-sat for get-unsat-core pairing
last_check_sat_status = ""
last_check_sat_cmd = Command(text="(check-sat)", head="check-sat")

if __name__ == "__main__":
    raise SystemExit(main())
