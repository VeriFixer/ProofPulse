# EXPANSIONS

## Context and main intention
There is prior published work in this area. The intention here is to push beyond baseline proof-coverage reporting and build a stronger, practical, and research-grade framework for proof understanding and debugging.

## Core expansion goals
1. Expand to lurking-axioms tracking.
   - Detect obligations that are discharged through non-obvious quantified facts, trigger behavior, or solver-side axioms.
   - Surface when proof success depends on "hidden" logical machinery rather than explicit local code/spec intent.

2. Support every language feature and complete tracking.

3. Perform granular tracking, including subexpression-level attribution.
   - Move beyond line-level attribution to expression- and subexpression-level dependency mapping.
   - Identify exactly which conjunct, bound, or arithmetic term matters in each discharged obligation.

4. Explore Z3 core minimization.
   - Investigate ways to reduce non-minimal unsat cores and redundant dependencies.
   - Compare baseline core extraction with shrinking/minimization heuristics and measure precision gains.

5. Evaluate utility with users.
   - Run user studies with verification practitioners and non-experts.
   - Measure whether explanations reduce debugging time, improve trust, and improve proof-maintenance decisions.

6. Integrate Tool on VScode

## IDEA TO THINL : Formal coverage metrics inpired by software tetsing
