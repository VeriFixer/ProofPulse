# Main commands
# Comboio que faz tudo (gerar boogie e z3 preparados para coverage report):
E gera os coverage reports
dafny verify Clover_abs.dfy --verification-coverage-report cov --log-format text --solver-option LOG_FILE=output.smt2 --bprint output.bpl 
z3 Clover_abs.dfy 
// Corre o z3
# Running with isolate assertions
dafny verify _USECASE_irrelevant_postconditions.dfy  --verification-coverage-report cov --log-format text --solver-option LOG_FILE=output.smt2 --bprint output.bpl   --isolate-assertions >> prover_log.txt

# Classification for complete coverage 
Code Lines:
- Covered Complete: if used to proof assertions that are postcondiitons (in proof dependency of them)
- Covered Warning: if used to proof assertions that are not related with postconditions
  - This in term represents a bad use case of using formal tools, and if a line was not being covered add an 
  assertion only for that line that is not related to the actual function... (this should be a warning)
  It is expected that for intance Main method only has warning of this kind
- Uncovered: Line not use in any assertion/postcondiiton proof 

Specification Lines:
- plain Asserts
  - Covered Complete: if used to proof assertion that are postcondtition
  [Before]
  - Covered Warning: If used to proof other assertion or itself that need to utilize at least one actual line of code (to restrictive)
  [Now]
  - Covered Warning: If used to proof other assertion or itself 
  - Uncovered: If used to proof only assertion or itself that do not uses any code lines (likely unecessary specification)

- postconditions
  - Covered Complete: If for proving the postcondition code lines of the method are used, and the postcondition is used to proof something when that method/function is called. Appears on proof depedencies like so: 
    _main_method_that_calls.dfy(9,8)-(9,18): ensures clause at _main_method_that_calls.dfy(2,13)-(2,16) from call
  - Covered Warning: If for proving the postcondition code lines of the method are used but it is not being used for anything the postcondiiton.
  - Uncovered: No code lines used to prove it (or assertions that use code lines)

- preconditions
  - Covered Complete: If precondition is strictly necessary used in proving its own postcondiiton
  - Covered Warning: If precondiiton is used to prove that a call can be made with that fucntion/method appears like so (this appears always like a warning it can indicate that restriction could be maybe removed) :
   _main_method_that_calls.dfy(10,8)-(10,19): requires clause at _main_method_that_calls.dfy(3,14)-(3,17) from call
  - Uncovered: precondition not necessary to prove postcondiiton and not being used

# Bugs 
Complete Full List of Bugs
Found bugs on Coverage can me find in the iles started with _ that are not _USECASE.
This will need to be adressed. Bug on assign, bug on calling functions/methods, lurking axioms with forall etc.

# Platform Tool objective 
For now: 
Generate HTLM (improvements in regards of current feature with):
FEATURES:
- Uncovered itens underlines at light blue (to be easy introduced in Vscode extension)
- Covered Complete itens left bar Dark blue tick (same to pass well to Vscode)
- Covered Test itens left bar median blue tick

- When clicking any elemnt (on the right full dependency tracker of that elemnt is shown, what elemnts is used to prove)
  and what is proving (proof graph basically)
  Related parts get highlighted

FEATURES SECOND PHASE
- If covered test was signalized as necessary (imagine main assertions, functions without postconditions)
  need on line {cov-test-to-complete: "Add comment justificaiton"} to signalize that assertion as complete with optional justification
- If uncovered and need to ignore add after line {cov-uncovered-to-complete: "Add comment justificaiton"} 

# Papers to read
A Polymorphic Intermediate Verification Language: Design and Logical Encoding 
(Nao muito relevante, mas boa leitura sobre tupos)
Triggerless Happy Intermediate Verification with a First-Order Prover
Free Facts: An Alternative to Inefficient Axioms in Dafny
(Interessante para perceber como aximoas e trigger funcionam)



# Well I opened some Issue in dafny will need to wait (will se if I can explore other frameworks like verus)
Deepseeks is thinking on those problemns that are happening:
- Z3's proof simplification is so aggressive that it's proving the postcondition without the explicit assignment
- The unsatisfiable core extraction is losing track of necessary dependencies
- Dafny's translation to Boogie/Z3 might be restructuring the code in ways that break the line-level mapping



# MM Considering other aproaches : 
Check this blog psot and paper:
https://kirancodes.me/posts/log-proof-localisation.html
https://ilyasergey.net/assets/pdf/papers/axolocl-cav25.pdf
https://matthias-brun.ch/assets/publications/verus_oopsla2023.pdf

Check Why3 (maybe it is easier to retrieve proof depencnies)


# Limitations
- The unsat core extracted form z3 is not guaranteed no be minimal. In fact a testcase bug out where that is the case 
/home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/tests/bug_useless_assigment_to_0_appears_on_core
possibly it depends ont he machine running as well the passing of this test
- Boogie/dafny invoke z3 as an external process, maybe I can change the call to make  alinear search algorithm of the minimum core from the core received (will have to think about it later)