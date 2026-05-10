## SLIDE 1 — Title (0:00–0:10)
> "This is ProofPulse — a tool that answers a question Dafny's verifier doesn't: which parts of your code and specification actually matter to the proof?"

## SLIDE 2 — The False Sense of Security (0:10–0:50)
> "Deductive verification proves that an implementation satisfies its specification. But it says nothing about specification *quality*. Consider this method — Dafny reports it as verified. A developer sees the green tick and moves on with confidence.
> But look at the postcondition: it claims 2 equals 3. And the precondition is mathematically impossible"
**Phase 2 (0:30–0:50):**
> "This is where ProofPulse comes in. By analyzing *what the proof actually used*, it reveals the truth: the precondition alone discharged everything, from false anything follows. The entire method body is red: uncovered, contributing nothing.
> Standard verification gave us a green tick. ProofPulse gives us a diagnosis — showing *why* the proof succeeded and exposing that it's weak."

## SLIDE 3 — Three-Valued Proof Coverage (0:50–1:20)
> "ProofPulse classifies every source element into three coverage levels. 
> CovComplete — green means this element actively contributes to proving a postcondition.
> CovTest — yellow,  flags elements that participate in the proof but aren't tied to a external code. In this example, the ensures clauses are yellow because no caller in scope depends on them yet — they're tested internally but not exercised externally.
> Uncovered — red,  means no proof obligation depends on this element at all. Here, the assignment `y := 0` inside `if x == 0` is redundant for the proof 
> Together, these three levels give developers actionable feedback that standard verification never provides."

## SLIDE 4 — Architecture (1:20–1:45)
> "ProofPulse works as a post-processor. We invoke Dafny with verification coverage reporting enabled — Dafny already produces a log that maps proof obligations to source spans. From that log, we construct a proof dependency graph
 We then run our three-valued classification over this graph. The classified graph is passed to both front-ends: the VSCode extension renders inline decorations, and the web viewer lets you explore the full dependency structure.

## SLIDE 5 — Closing (4:40–5:00)
> "Just as a pulse check distinguishes vitality from the mere absence of symptoms, ProofPulse reveals defects in proofs that, while technically passing, remain semantically weak. It's open-source, runs as a VSCode extension, requires only Dafny.

