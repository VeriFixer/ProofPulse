#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence


QUERY_COMMANDS = {
    "check-sat",
    "check-sat-assuming",
    "get-unsat-core",
    "get-model",
    "get-assignment",
    "get-value",
    "get-proof",
    "get-info",
    "echo",
}

STATUS_RE = re.compile(r"(?m)^(sat|unsat|unknown)\s*$")
CORE_MARKER = "__UNSAT_CORE_MARKER__"


class SMT2Error(Exception):
    pass


@dataclass(frozen=True)
class Command:
    text: str
    head: Optional[str]
    label: Optional[str] = None


def split_top_level(text: str) -> List[str]:
    """Split SMT-LIB text into top-level S-expressions.

    Handles comments, double-quoted strings, and bar-quoted symbols.
    """
    items: List[str] = []
    buf: List[str] = []
    depth = 0
    in_comment = False
    in_string = False
    in_bar = False
    escape = False

    for ch in text:
        if in_comment:
            if ch == "\n":
                in_comment = False
                if depth > 0:
                    buf.append(ch)
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
            in_comment = True
            continue

        if ch == '"':
            if depth > 0:
                buf.append(ch)
            in_string = True
            continue

        if ch == "|":
            if depth > 0:
                buf.append(ch)
            in_bar = True
            continue

        if ch == "(":
            if depth == 0:
                buf = []
            buf.append(ch)
            depth += 1
            continue

        if ch == ")":
            if depth == 0:
                raise SMT2Error("Unbalanced parentheses while parsing SMT2 file")
            buf.append(ch)
            depth -= 1
            if depth == 0:
                items.append("".join(buf).strip())
                buf = []
            continue

        if depth > 0:
            buf.append(ch)

    if depth != 0 or in_string or in_bar:
        raise SMT2Error("Incomplete top-level SMT2 expression")

    return [item for item in items if item]


def first_head(expr: str) -> Optional[str]:
    m = re.match(r"\(\s*([^\s()]+)", expr, flags=re.DOTALL)
    return m.group(1) if m else None


def parse_positive_int_command(expr: str, expected_head: str) -> int:
    m = re.fullmatch(r"\(\s*" + re.escape(expected_head) + r"\s+(\d+)\s*\)", expr.strip())
    if not m:
        raise SMT2Error(f"Unsupported command form: {expr}")
    return int(m.group(1))


def extract_named_label(assert_cmd: str) -> Optional[str]:
    if first_head(assert_cmd) != "assert":
        return None
    m = re.search(r":named\s+([^\s()]+)", assert_cmd, flags=re.DOTALL)
    return m.group(1) if m else None


def parse_commands(path: Path) -> List[Command]:
    text = path.read_text(encoding="utf-8", errors="replace")
    raw = split_top_level(text)
    cmds: List[Command] = []
    for expr in raw:
        head = first_head(expr)
        label = extract_named_label(expr)
        cmds.append(Command(text=expr, head=head, label=label))
    return cmds


def build_script(commands: Sequence[Command], kept_labels: Optional[set[str]], query_block: Sequence[Command], add_marker: bool) -> str:
    parts: List[str] = []
    for cmd in commands:
        if cmd.label is not None and kept_labels is not None and cmd.label not in kept_labels:
            continue
        parts.append(cmd.text)
    if add_marker:
        for q in query_block:
            if q.head == "get-unsat-core":
                parts.append(f'(echo "{CORE_MARKER}")')
            parts.append(q.text)
    else:
        parts.extend(q.text for q in query_block)
    return "\n".join(parts) + "\n"


def run_z3(z3_bin: str, script_text: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False, encoding="utf-8") as f:
        f.write(script_text)
        tmp_path = f.name
    try:
        proc = subprocess.run(
            [z3_bin, "-smt2", tmp_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
    finally:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
    return proc


def extract_first_balanced_sexpr(text: str) -> Optional[str]:
    start = text.find("(")
    if start == -1:
        return None

    depth = 0
    in_string = False
    in_bar = False
    escape = False

    for i in range(start, len(text)):
        ch = text[i]
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue
        if in_bar:
            if ch == "|":
                in_bar = False
            continue
        if ch == '"':
            in_string = True
            continue
        if ch == "|":
            in_bar = True
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
    return None


def parse_core_expr(expr: str) -> List[str]:
    expr = expr.strip()
    if not expr.startswith("(") or not expr.endswith(")"):
        raise SMT2Error(f"Malformed unsat core S-expression: {expr!r}")
    inner = expr[1:-1].strip()
    if not inner:
        return []
    return inner.split()


def parse_status(stdout: str) -> str:
    m = STATUS_RE.search(stdout)
    if not m:
        raise SMT2Error(f"Could not find solver status in output:\n{stdout}")
    return m.group(1)


def parse_core_from_marked_output(stdout: str) -> List[str]:
    marker_pos = stdout.find(CORE_MARKER)
    if marker_pos == -1:
        raise SMT2Error(f"Did not find unsat-core marker in output:\n{stdout}")
    tail = stdout[marker_pos + len(CORE_MARKER):]
    expr = extract_first_balanced_sexpr(tail)
    if expr is None:
        raise SMT2Error(f"Could not parse unsat core after marker:\n{stdout}")
    return parse_core_expr(expr)


def current_context(frames: Sequence[List[Command]]) -> List[Command]:
    out: List[Command] = []
    for frame in frames:
        out.extend(frame)
    return out


def active_labels_in_context(commands: Sequence[Command]) -> set[str]:
    labels = [cmd.label for cmd in commands if cmd.label is not None]
    seen = set()
    dups = []
    for lbl in labels:
        if lbl in seen:
            dups.append(lbl)
        seen.add(lbl)
    if dups:
        raise SMT2Error(f"Duplicate active labels in same solver state: {', '.join(sorted(set(dups)))}")
    return seen


def normalize_core(core: Sequence[str], active_labels: set[str]) -> List[str]:
    seen = set()
    out: List[str] = []
    for lbl in core:
        if lbl not in active_labels:
            raise SMT2Error(f"Z3 returned label not active in current context: {lbl}")
        if lbl not in seen:
            seen.add(lbl)
            out.append(lbl)
    return out


def minimize_core_for_block(
    z3_bin: str,
    context_cmds: Sequence[Command],
    query_block: Sequence[Command],
    initial_core: Sequence[str],
) -> List[str]:
    active_labels = active_labels_in_context(context_cmds)
    active = normalize_core(initial_core, active_labels)
    kept = set(active)

    i = 0
    while i < len(active):
        label = active[i]
        trial = active[:i] + active[i + 1:]
        trial_kept = set(trial)
        script = build_script(context_cmds, trial_kept, query_block, add_marker=True)
        proc = run_z3(z3_bin, script)
        if proc.returncode not in (0, 1):
            raise SMT2Error(f"Z3 failed during minimization.\nstdout:\n{proc.stdout}\n\nstderr:\n{proc.stderr}")
        status = parse_status(proc.stdout)
        if status == "unsat":
            new_core = parse_core_from_marked_output(proc.stdout)
            new_core = normalize_core(new_core, trial_kept)
            active = new_core
            kept = set(active)
            i = 0
        else:
            i += 1

    return active


def process_file(z3_bin: str, commands: Sequence[Command], quiet: bool) -> str:
    frames: List[List[Command]] = [[]]
    out_chunks: List[str] = []
    i = 0
    block_index = 0

    while i < len(commands):
        cmd = commands[i]
        head = cmd.head

        if head == "push":
            count = parse_positive_int_command(cmd.text, "push")
            for _ in range(count):
                frames.append([])
            i += 1
            continue

        if head == "pop":
            count = parse_positive_int_command(cmd.text, "pop")
            if count >= len(frames):
                raise SMT2Error(f"Pop underflow: {cmd.text}")
            for _ in range(count):
                frames.pop()
            i += 1
            continue

        if head == "reset":
            frames = [[]]
            i += 1
            continue

        if head == "check-sat" or head == "check-sat-assuming":
            block_index += 1
            query_block: List[Command] = [cmd]
            i += 1
            while i < len(commands) and commands[i].head in QUERY_COMMANDS and commands[i].head not in {"check-sat", "check-sat-assuming"}:
                query_block.append(commands[i])
                i += 1

            context_cmds = current_context(frames)
            original_script = build_script(context_cmds, None, query_block, add_marker=True)
            proc = run_z3(z3_bin, original_script)
            if proc.returncode not in (0, 1):
                raise SMT2Error(f"Z3 failed on query block {block_index}.\nstdout:\n{proc.stdout}\n\nstderr:\n{proc.stderr}")

            status = parse_status(proc.stdout)
            requested_core = any(q.head == "get-unsat-core" for q in query_block)

            if not requested_core or status != "unsat":
                rendered = run_z3(z3_bin, build_script(context_cmds, None, query_block, add_marker=False))
                if rendered.returncode not in (0, 1):
                    raise SMT2Error(f"Z3 failed rendering block {block_index}.\nstdout:\n{rendered.stdout}\n\nstderr:\n{rendered.stderr}")
                out_chunks.append(rendered.stdout)
                if rendered.stderr and not quiet:
                    out_chunks.append(rendered.stderr)
                continue

            initial_core = parse_core_from_marked_output(proc.stdout)
            minimized_core = minimize_core_for_block(z3_bin, context_cmds, query_block, initial_core)
            if not quiet:
                sys.stderr.write(
                    f"; [block {block_index}] initial core size {len(initial_core)} -> minimized size {len(minimized_core)}\n"
                )
            final_script = build_script(context_cmds, set(minimized_core), query_block, add_marker=False)
            final_proc = run_z3(z3_bin, final_script)
            if final_proc.returncode not in (0, 1):
                raise SMT2Error(f"Z3 failed rendering minimized block {block_index}.\nstdout:\n{final_proc.stdout}\n\nstderr:\n{final_proc.stderr}")
            out_chunks.append(final_proc.stdout)
            if final_proc.stderr and not quiet:
                out_chunks.append(final_proc.stderr)
            continue

        frames[-1].append(cmd)
        i += 1

    return "".join(out_chunks)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Run an SMT2 trace with push/pop/reset and replace each reported unsat core by a core-driven minimized core. "
            "For every query block containing check-sat ... get-unsat-core, the script minimizes only the active named assertions in that current solver state."
        )
    )
    ap.add_argument("smt2", type=Path, help="Input SMT2 trace")
    ap.add_argument("--z3", default="z3", help="Path to z3 binary")
    ap.add_argument("--output", type=Path, default=None, help="Optional file to write the transformed run output")
    ap.add_argument("--quiet", action="store_true", help="Suppress progress messages on stderr")
    args = ap.parse_args()

    try:
        commands = parse_commands(args.smt2)
        output = process_file(args.z3, commands, quiet=args.quiet)
    except FileNotFoundError:
        print(f"error: could not find z3 binary: {args.z3}", file=sys.stderr)
        return 2
    except SMT2Error as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if args.output is not None:
        args.output.write_text(output, encoding="utf-8")
    else:
        sys.stdout.write(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
