/**
 * Facts that supplied trigger terms, read from z3's trace.
 *
 * z3's unsat core leaves out a fact whose only part in the proof was to supply
 * a term that triggered a quantifier (a "lurking" fact). Following Axolocl
 * (Gopinathan et al., CAV 2025), the trace tells which terms each quantifier
 * instantiation matched on and which instantiation created each term:
 *
 * - start from the instantiations of quantifiers the kept facts hold (or that
 *   no tracked fact holds: those are always present);
 * - walk each match's trigger terms back to the instantiation that created
 *   them, keeping the fact that holds its quantifier;
 * - a trigger term no instantiation created comes from the formula itself:
 *   keep a tracked fact that contains it, unless a kept fact already does.
 *
 * Unlike Axolocl this also credits facts without quantifiers, and works on
 * z3's own term graph, so it needs no quantifier ids (Dafny's SMT has none).
 *
 * Tracked facts are recognised by the encoding Boogie uses for coverage: a
 * guard constant `g` named by `(assert (! g :named aux$$...))`, an assumed fact
 * `(=> g F)` and an asserted one `(and g F)`.
 */

/** One term of the trace. z3 reuses ids, so terms are objects, not ids. */
interface Term {
  name: string;
  args: Term[];
  /** Index of the match whose instantiation created it; -1 for terms of the formula. */
  createdBy: number;
}

interface Match {
  quantifier: Term;
  /** Terms the match used: trigger terms and the terms of equalities it matched modulo. */
  blame: Term[];
  instantiated: boolean;
}

export interface TriggerTrace {
  /** Label (`aux$$...`) of each tracked fact → its guard constant. */
  guards: Map<string, Term>;
  /** Guard constant → the fact bodies it guards. */
  bodies: Map<Term, Term[]>;
  matches: Match[];
}

const LABEL_PREFIX = "aux$$";

/** Parse a z3 trace (`trace=true`). Unknown lines are skipped. */
export function parseTriggerTrace(text: string): TriggerTrace {
  const byId = new Map<string, Term>();
  const guards = new Map<string, Term>();
  const bodies = new Map<Term, Term[]>();
  const matches: Match[] = [];
  const matchByHash = new Map<string, number>();
  // An instantiation creates its terms just before its `[instance]` line (after
  // the last line that is not a term) and inside the instance block.
  let pending: Term[] = [];
  let instance = -1;

  const term = (id: string): Term | undefined => byId.get(id);
  const addBody = (guard: Term, body: Term): void => {
    const list = bodies.get(guard);
    if (list) list.push(body); else bodies.set(guard, [body]);
  };

  for (const line of text.split("\n")) {
    const sp = line.indexOf(" ");
    const tag = sp < 0 ? line : line.slice(0, sp);
    const rest = sp < 0 ? [] : line.slice(sp + 1).trim().split(/\s+/);

    if (tag === "[mk-app]" || tag === "[mk-quant]" || tag === "[mk-var]" || tag === "[mk-lambda]") {
      const [id, name, ...argIds] = rest;
      // [mk-quant] #id name nvars pattern... body
      const ids = tag === "[mk-quant]" || tag === "[mk-lambda]" ? argIds.slice(1) : tag === "[mk-var]" ? [] : argIds;
      const t: Term = {
        name: tag === "[mk-app]" ? name : `${tag}${name}`,
        args: ids.filter((a) => a.startsWith("#")).map(term).filter((a): a is Term => !!a),
        createdBy: instance,
      };
      byId.set(id, t);
      if (instance < 0) pending.push(t);
      if (tag !== "[mk-app]") continue;
      // (=> label guard): the named assertion that switches a tracked fact on
      if (name === "=>" && t.args.length === 2 && t.args[0].args.length === 0 && t.args[0].name.startsWith(LABEL_PREFIX)) {
        guards.set(t.args[0].name, t.args[1]);
        continue;
      }
      // (=> guard F): an assumed fact; (and ... guard F ...): an asserted one
      if (name === "=>" && t.args.length === 2 && isGuard(t.args[0])) addBody(t.args[0], t.args[1]);
      if (name === "and") {
        for (const g of t.args.filter(isGuard)) for (const b of t.args) if (b !== g) addBody(g, b);
      }
    } else if (tag === "[new-match]") {
      // [new-match] hash #quant #pattern #binding... ; #blame... (#eq-a #eq-b)...
      const semi = rest.indexOf(";");
      const quantifier = term(rest[1]);
      if (!quantifier) continue;
      const blameIds = semi < 0 ? [] : rest.slice(semi + 1).map((b) => b.replace(/[()]/g, "")).filter((b) => b.startsWith("#"));
      matchByHash.set(rest[0], matches.length);
      pending = [];
      matches.push({ quantifier, blame: blameIds.map(term).filter((b): b is Term => !!b), instantiated: false });
    } else if (tag === "[instance]") {
      const index = matchByHash.get(rest[0]);
      if (index !== undefined) {
        matches[index].instantiated = true;
        for (const t of pending) t.createdBy = index;
        instance = index;
      }
      pending = [];
    } else if (tag === "[end-of-instance]") {
      instance = -1;
      pending = [];
    } else if (instance < 0 && !tag.startsWith("[attach-")) {
      pending = [];
    }
  }

  function isGuard(t: Term): boolean {
    for (const g of guards.values()) if (g === t) return true;
    return false;
  }

  return { guards, bodies, matches };
}

/** Every term reachable from `roots` (quantifier bodies and patterns included). */
function reachable(roots: Term[]): Set<Term> {
  const seen = new Set<Term>();
  const work = [...roots];
  while (work.length > 0) {
    const t = work.pop()!;
    if (seen.has(t)) continue;
    seen.add(t);
    work.push(...t.args);
  }
  return seen;
}

/**
 * Labels of tracked facts, beyond `kept`, that supplied trigger terms to the
 * instantiations the kept facts rely on. Candidates only: the caller checks
 * that they make the kept facts prove the goal.
 */
export function triggerSuppliers(trace: TriggerTrace, kept: ReadonlySet<string>): string[] {
  const labels = [...trace.guards.keys()];
  const contents = new Map<string, Set<Term>>();
  for (const label of labels) contents.set(label, reachable(trace.bodies.get(trace.guards.get(label)!) ?? []));

  const keep = new Set(kept);
  const added: string[] = [];
  const holders = (t: Term): string[] => labels.filter((l) => contents.get(l)!.has(t));
  const add = (label: string): void => {
    if (keep.has(label)) return;
    keep.add(label);
    added.push(label);
    // A fact nested in another fact's body is switched off with it
    const guard = trace.guards.get(label)!;
    for (const outer of holders(guard)) add(outer);
  };

  // Quantifiers held by no tracked fact are always present.
  const quantifierPresent = (q: Term): boolean => {
    const h = holders(q);
    return h.length === 0 || h.some((l) => keep.has(l));
  };

  const done = new Set<number>();
  const work = trace.matches.flatMap((m, i) => (m.instantiated && quantifierPresent(m.quantifier) ? [i] : []));
  while (work.length > 0) {
    const i = work.pop()!;
    if (done.has(i)) continue;
    done.add(i);
    for (const t of trace.matches[i].blame) {
      if (t.createdBy >= 0) {
        // Created by another instantiation: its quantifier must be present too
        const producer = trace.matches[t.createdBy];
        if (!quantifierPresent(producer.quantifier)) add(holders(producer.quantifier)[0]);
        work.push(t.createdBy);
        continue;
      }
      const h = holders(t);
      if (h.length > 0 && !h.some((l) => keep.has(l))) add(h[0]);
    }
  }
  return added;
}
