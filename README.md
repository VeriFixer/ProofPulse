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

# Evaluation 
- For now I do have the samll dataset (after having MVP need to expand)

# Options 
This flag is not passed to z3:
(set-option :smt.core.minimize true)
maybe it could be passed need to test
s.set("sat.core.minimize","true")  # For Bit-vector theories
s.set("smt.core.minimize","true")  # For general SMT 

# Well formness 
Most well forness checks dont use most things, but they are not criticial I believe. However need to unserstand
Exactly what are well formed checks


# Papers to read
A Polymorphic Intermediate Verification Language: Design and Logical Encoding 
(Nao muito relevante, mas boa leitura sobre tupos)
Triggerless Happy Intermediate Verification with a First-Order Prover
Free Facts: An Alternative to Inefficient Axioms in Dafny
(Interessante para perceber como aximoas e trigger funcionam)
















# Objectives
This Repo explores coverage Ideas apllied to SMT based verification-aware languages (particulary Dafny).

# Roadmap 
- 20 Examples datase gatherer
- Use provided Dafny tools of Coverage and see the results
- (The rest of the steps and obectives are in other files)



# Dafny has 4 help menus
This tow are mostly eqaul
dafny --help 
dafny --help-internal

this shows all options ther exist a lot
dafny -? 

# Usefull options (acessible with old cli only)
To get xml output
 dafny /xml:helper.txt ../dataset/Clover_abs.dfy 

  /coverage:<file>
      The compiler emits branch-coverage calls and outputs into <file> a
      legend that gives a description of each source-location identifier
      used in the branch-coverage calls. (Use - as <file> to print to the
      console.)
      
/extractCounterexample
      If verification fails, report a detailed counterexample for the
      first failing assertion (experimental).
  ---- Verification-condition generation options -----------------------------

Nao claro se esta liveVariableAnalysys corresponde apenas ao codigo ou considera as poscondicoes tambem

/liveVariableAnalysis:<c>
                0 = do not perform live variable analysis
                1 = perform live variable analysis (default)
                2 = perform interprocedural live variable analysis

/verifySnapshots:<n>
                verify several program snapshots (named <filename>.v0.bpl
                to <filename>.vN.bpl) using verification result caching:
                0 - do not use any verification result caching (default)
                1 - use the basic verification result caching
                2 - use the more advanced verification result caching
                3 - use the more advanced caching and report errors according
                    to the new source locations for errors and their
                    related locations (but not /errorTrace and CaptureState
                    locations)
PArecem ser mais boogie options
/trackVerificationCoverage
                Track and report which program elements labeled with an
                `{:id ...}` attribute were necessary to complete verification.
                Assumptions, assertions, requires clauses, ensures clauses,
                assignments, and calls can be labeled for inclusion in this
                report. This generalizes and replaces the previous
                (undocumented) `/printNecessaryAssertions` option.
/warnVacuousProofs
                Automatically add missing `{:id ...}` attributes to assumptions,
                assertions, requires clauses, ensures clauses, and calls; enable the
                `/trackVerificationCoverage` option; and warn when proof goals are
                not covered by a proof.
  /vcsCores:<n>
                Try to verify <n> VCs at once. Defaults to 1.
  /vcsLoad:<f>  Sets vcsCores to the machine's ProcessorCount * f,
                rounded to the nearest integer (where 0.0 <= f <= 3.0),
                but never to less than 1.

13.6.1.10. dafny test
This command (verifies and compiles the program and) runs every method in the program that is annotated with the {:test} attribute. Verification can be disabled using the --no-verify option. dafny test also accepts all other options of the dafny build command. In particular, it accepts the --target option that specifies the programming language used in the build and execution phases.

dafny test also accepts these options:

-spill-translation - (default disabled) when enabled the compilation artifacts are retained
--output - gives the folder and filename root for compilation artifacts
--methods-to-test - the value is a (.NET) regular expression that is matched against the fully qualified name of the method; only those methods that match are tested
--coverage-report - the value is a directory in which Dafny will save an html coverage report highlighting parts of the program that execution of the tests covered.

13.6.1.12. dafny generate-tests
This experimental command allows generating tests from Dafny programs. The tests provide complete coverage of the implementation and one can execute them using the dafny test command. Dafny can target different notions of coverage while generating tests, with basic-block coverage being the recommended setting. Basic blocks are extracted from the Boogie representation of the Dafny program, with one basic block corresponding to a statement or a non-short-circuiting subexpression in the Dafny code. The underlying implementation uses the verifier to reason about the reachability of different basic blocks in the program and infers necessary test inputs from counterexamples.

For example, this code (as the file program.dfy)

module M {
  function {:testEntry} Min(a: int, b: int): int {
    if a < b then a else b
  }
}
and this command-line

dafny generate-tests Block program.dfy
produce two tests:

include "program.dfy"
module UnitTests {
  import M
  method {:test} Test0() {
    var r0 := M.Min(0, 0);
  }
  method {:test} Test1() {
    var r0 := M.Min(0, 1);
  }
}
The two tests together cover every basic block within the Min function in the input program. Note that the Min function is annotated with the {:testEntry} attribute. This attribute marks Min as the entry point for all generated tests, and there must always be at least one method or function so annotated. Another requirement is that any top-level declaration that is not itself a module (such as class, method, function, etc.) must be a member of an explicitly named module, which is called M in the example above.

This command is under development and not yet fully functional.

13.6.1.13. Inlining
By default, when asked to generate tests, Dafny will produce unit tests, which guarantee coverage of basic blocks within the method they call but not within any of its callees. By contrast, system-level tests can guarantee coverage of a large part of the program while at the same time using a single method as an entry point. In order to prompt Dafny to generate system-level tests, one must use the {:testInline} attribute.

For example, this code (as the file program.dfy)

module M {
  function {:testInline} Min(a: int, b: int): int {
    if a < b then a else b
  }
  method {:testEntry} Max(a: int, b: int) returns (c: int)
    // the tests convert the postcondition below into runtime check:
    ensures c == if a > b then a else b
  {
    return -Min(-a, -b);
  }
}
and this command-line

dafny generate-tests Block program.dfy
produce two tests:

include "program.dfy"
module UnitTests {
  import M
  method {:test} Test0() {
    var r0 := M.Max(7719, 7720);
    expect r0 == if 7719 > 7720 then 7719 else 7720;
  }
  method {:test} Test1() {
    var r0 := M.Max(1, 0);
    expect r0 == if 1 > 0 then 1 else 0;
  }
}
Without the use of the {:testInline} attribute in the example above, Dafny will only generate a single test because there is only one basic-block within the Max method itself – all the branching occurs within the Min function. Note also that Dafny automatically converts all non-ghost postconditions on the method under tests into expect statements, which the compiler translates to runtime checks in the target language of choice.

When the inlined method or function is recursive, it might be necessary to unroll the recursion several times to get adequate code coverage. The depth of recursion unrolling should be provided as an integer argument to the {:testInline} attribute. For example, in the program below, the function Mod3 is annotated with {:testInline 2} and will, therefore, be unrolled twice during test generation. The function naively implements division by repeatedly and recursively subtracting 3 from its argument, and it returns the remainder of the division, which is one of the three base cases. Because the TestEntry method calls Mod3 with an argument that is guaranteed to be at least 3, the base case will never occur on first iteration, and the function must be unrolled at least twice for Dafny to generate tests covering any of the base cases:

module M {
  function {:testInline 2} Mod3 (n: nat): nat
    decreases n
  {
    if n == 0 then 0 else
    if n == 1 then 1 else
    if n == 2 then 2 else
    Mod3(n-3)
  }
  method {:testEntry} TestEntry(n: nat) returns (r: nat)
    requires n >= 3
  {
    r := Mod3(n);
  }
}

(From dafny documentation)

--coverage-report - the value is a directory in which Dafny will save an html coverage report highlighting parts of the program that the generated tests are expected to cove

13.6.1.15. dafny find-dead-code
This experimental command finds dead code in a program, that is, basic-blocks within a method that are not reachable by any inputs that satisfy the method’s preconditions. The underlying implementation is identical to that of dafny generate-tests command and can be controlled by the same command line options and method attributes.

For example, this code (as the file program.dfy)

module M {
  function {:testEntry} DescribeProduct(a: int): string {
    if a * a < 0 
    then "Product is negative"
    else "Product is nonnegative"
  }
}
and this command-line

dafny find-dead-code program.dfy
produce this output:

program.dfy(5,9) is reachable.
program.dfy(3,4):initialstate is reachable.
program.dfy.dfy(5,9)#elseBranch is reachable.
program.dfy.dfy(4,9)#thenBranch is potentially unreachable.
Out of 4 basic blocks, 3 are reachable.
Dafny reports that the then branch of the condition is potentially unreachable because the verifier proves that no input can reach it. In this case, this is to be expected, since the product of two numbers can never be negative. In practice, find-dead-code command can produce both false positives (if the reachability query times out) and false negatives (if the verifier cannot prove true unreachability), so the results of such a report should always be reviewed


# Coverage of proofs
13.7.5. Analyzing proof dependencies
When Dafny successfully verifies a particular definition, it can ask the solver for information about what parts of the program were actually used in completing the proof. The program components that can potentially form part of a proof include:

assert statements (and the implicit assumption that they hold in subsequent code),
implicit assertions (such as array or sequence bounds checks),
assume statements,
ensures clauses,
requires clauses,
function definitions,
method calls, and
assignment statements.
Understanding what portions of the program the proof depended on can help identify mistakes, and to better understand the structure of your proof (which can help when optimizing it, among other things). In particular, there are two key dependency structures that tend to indicate mistakes, both focused on what parts of the program were not included in the proof.

Redundant assumptions. In some cases, a proof can be completed without the need of certain assume statements or requires clauses. This situation might represent a mistake, and when the mistake is corrected those program elements may become required. However, they may also simply be redundant, and the program will become simpler if they’re removed. Dafny will report assumptions of this form when verifying with the flag --warn-redundant-assumptions. Note that assert statements may be warned about, as well, indicating that the fact proved by the assertion wasn’t needed to prove anything else in the program.

Contradictory assumptions. If the combination of all assumptions in scope at a particular program point is contradictory, anything can be proved at that point. This indicates the serious situation that, unless done on purpose in a proof by contradiction, your proof may be entirely vacuous. It therefore may not say what you intended, giving you a false sense of confidence. The --warn-contradictory-assumptions flag instructs Dafny to warn about any assertion that was proved through the use of contradictions between assumptions. If a particular assert statement is part of an intentional proof by contradiction, annotating it with the {:contradiction} attribute will silence this warning.

These options can be specified in dfyconfig.toml, and this is typically the most convenient way to use them with the IDE.

More detailed information is available using either the --log-format text or --verification-coverage-report option to dafny verify. The former will include a list of proof dependencies (including source location and description) alongside every assertion batch in the generated log whenever one of the two warning options above is also included. The latter will produce a highlighted HTML version of your source code, in the same format used by dafny test --coverage-report and dafny generate-tests --verification-coverage-report, indicating which parts of the program were used, not used, or partly used in the verification of the entire program.
(descoberto)



# Comando para gerar a coverage formal 'e entao
dafny verify --verification-coverage-report file reportFolder 

Nao entendo o Report no caso mesmo simples do Clover_abs por exemplo
Apare com umas cores mas nao da mesmo para perceber o que falhou


# Steps: 
Consigo correr coverage report formal! 
Nao percebo minimamente os resultados o grafismo parece mal (tenho que perceber mais a fundo o que estou a ver)
Posso perguntar ao implementador se nao perceber de todo apos ver com muita mais calma
https://github.com/dafny-lang/dafny/pull/4625

Na verdade o mais acil tem ar de usar a proof dependecy toda:
--log-format text
dafny verify Clover_abs_more_assert.dfy --verification-coverage-report cov --log-format text


# It seems that the problem i was having is that the program was consider the group of assertions together
What is faster but worse for this analysys for sure
Running in this way solves that:
dafny verify Clover_abs.dfy --verification-coverage-report cov --log-format text --isolate-assertions

Did not work at all really (it complicated the HTML)

Things on proof depedndency (aquilo que me anda a escapar):
https://dafny.org/blog/2023/10/27/proof-dependencies/
(this indicates also infomration on: 
--warn-contradictory-assumptions,
--warn-redundant-assumptions,
)



# From That same link 


Dafny includes a verification logger that will describe the status of and statistics about each verification goal in the program. When proof dependency analysis is enabled, this will include information about which potential proof dependencies did or did not take place in the actual proof. This information will only be included if one of the other flags enabling proof dependency analysis is enabled, however. So, if we analyze the binary search example using the command dafny verify --log-format text --warn-redundant-assertions, the output will include the following text.

Theory and implementation
Internally, Dafny's proof dependency analysis is built on the common SMT feature of unsatisfiable cores. Dafny encodes each verification goal as an SMT query that negates the original goal. This means that a conclusion that the negated goal is unsatisfiable (i.e., no value exists that will make it true) means that the original goal is valid (i.e., true for all possible values). Many SMT solvers, including the Z3 solver that Dafny uses by default, can accompany a conclusion of “unsatisfiable” with a subset of the sub-expressions (clauses, in SMT terminology) from the original goal that is still unsatisfiable. This subset is generally smaller than the original formula, though it is not guaranteed to be so, and is not guaranteed to be minimal.

Because unsatisfiable cores are not guaranteed to be minimal, Dafny may sometimes fail to warn about some goals that are proved using a contradiction, or some assumptions that are not ultimately necessary. In our early experience, however, Dafny does produce useful warnings for all large code bases we've tried it on.




# Other cool tings to consider verification otimizations
https://dafny.org/latest/VerificationOptimization/VerificationOptimization

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

# This gemini deep research query was very good 
https://docs.google.com/document/d/17VnWyMugNQOA0u6l3SfTsmubEeHletylm9Wt-AkDWe4/edit?tab=t.0

Fiz outro query ao gemini esta nos docs mas de longe pior (nao direcionei para rust Verus, ou why3). Estou um pouco a deriva. Vou ler aqueles 2 papers mais o de verus. tricky

# Optimizing Bit vecotr verification
https://github.com/dafny-lang/dafny/wiki/Bit-Vector-Cookbook
# Optmizing verification
https://dafny.org/latest/VerificationOptimization/VerificationOptimization