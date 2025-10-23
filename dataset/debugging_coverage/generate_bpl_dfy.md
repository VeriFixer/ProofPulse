There are a few ways to do this. One way is like this:
 dafny verify --solver-option VERBOSITY=2 file.dfy
A more useful way is to generate the SMTLIB file passed into the theorem prover like this:
 dafny verify --solver-option LOG_FILE=output.smt2 file.dfy
Finally, you can also generate the intermediate Boogie file like this as well:
 dafny verify --bprint file.bpl file.dfy

 Run only boogie now to extract proof dependencies
 boogie Clover_abs.bpl /printInstrumented /tracePOs /printPruned:Pruned_Boogie  /vcsSplitOnEveryAssert /proverLog:Plain_Boogie_verig.log


Gerar boogie e smt diretamente do topo do dafny
Estas sao da isabel nao funcionam tao bem (as outras sao melhorzitas)
Boogie
dafny <program> /print:<output_file>
Z3
dafny <program> /proverLog:<output-file> ou então dafny verify <program> --solver-log <output-file>







# Comboio que faz tudo (gerar boogie e z3 preparados para coverage report):
dafny verify Clover_abs.dfy --verification-coverage-report cov --solver-option LOG_FILE=output.smt2 --bprint output.bpl

# Para gerar apenas unsats diretor apos esse ficheiro gerado
Apos isso posso gerar o unsat core diretamente no z3
··• z3 -smt2 output.smt2 
unsat
(:rlimit 4940)
(aux$$assert$$id8 aux$$assert$$id9 aux$$assert$$id13 aux$$assume$$id10 aux$$assert$$id11)

Inspecionando o bpl encontro
ensures {:id "id8"} x#0 >= LitInt(0) ==> x#0 == y#0;
ensures {:id "id9"} x#0 < 0 ==> x#0 + y#0 == LitInt(0);

y#0 := x#0;
defass#y#0 := true;
assume {:captureState "Clover_abs.dfy(8,12)"} true;
assert {:id "id13"} defass#y#0;

y#0 := 0 - x#0;
defass#y#0 := true;
assume {:captureState "Clover_abs.dfy(6,13)"} true;
assert {:id "id11"} defass#y#0;


Esta nao esta no fim da funcao: (mas tmb nao corresponde a nenhuma linha do codigo):
assert {:id "id14"} defass#y#0;


id13 Nao exsite!!!

mmm (parece-me que o mapping esta errado), aquelas todas aparecem no unsat core mais uma named assertion id13 que nao esta presente no Boogie! 


# Logo acho que 'e um bug no dafny a converter boogie para dafny no mapeamento

Great i am doing progress, i already discover whchi lines are being used in boogie due to the named unsumptions of the unsat core but! When generating the dafny coveraeg report that tells the proof dependencies.

I get this:
Dafny program verifier finished with 1 verified, 0 errors

Results for Abs (correctness)
  Overall outcome: Correct
  Overall time: 00:00:00.1025944
  Overall resource count: 4924
  Maximum assertion batch time: 00:00:00.1025944
  Maximum assertion batch resource count: 4924

  Assertion batch 1:
    Outcome: Valid
    Duration: 00:00:00.1025944
    Resource count: 4924

    Assertions:
      Clover_abs.dfy(8,5): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
      Clover_abs.dfy(2,21): this postcondition holds
      Clover_abs.dfy(3,22): this postcondition holds
      Clover_abs.dfy(6,5): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point

    Proof dependencies:
      Clover_abs.dfy(2,20)-(2,23): ensures clause
      Clover_abs.dfy(3,19)-(3,24): ensures clause
      Clover_abs.dfy(6,5)-(6,14): assignment (or return)
      Clover_abs.dfy(6,5)-(6,14): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
      Clover_abs.dfy(8,5)-(8,13): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point

    Unused by proof:
      Clover_abs.dfy(8,5)-(8,13): assignment (or return)
      Clover_abs.dfy(10,1)-(10,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point

░▒▓ 

the thing is that line 
      Clover_abs.dfy(8,5)-(8,13): assignment (or return)

is this:
method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    return -x;
  } else {
    return x; //this is the line
  }
}

and that was used in the unsat core seing the bpl 
implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Abs (correctness)"} Impl$$_module.__default.Abs(x#0: int) returns (defass#y#0: bool, y#0: int, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;

    // AddMethodImpl: Abs, Impl$$_module.__default.Abs
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "Clover_abs.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/debugging_coverage/Clover_abs.dfy(5,3)
    assume true;
    if (x#0 < 0)
    {
        // ----- return statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/debugging_coverage/Clover_abs.dfy(6,5)
        // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/debugging_coverage/Clover_abs.dfy(6,5)
        assume true;
        assume true;
        y#0 := 0 - x#0;
        defass#y#0 := true;
        assume {:captureState "Clover_abs.dfy(6,13)"} true;
        assert {:id "id11"} defass#y#0;
        return;
    }
    else
    {
        // ----- return statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/debugging_coverage/Clover_abs.dfy(8,5)
        // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/debugging_coverage/Clover_abs.dfy(8,5)
        assume true;
        assume true;
        y#0 := x#0;
        defass#y#0 := true;
        assume {:captureState "Clover_abs.dfy(8,12)"} true;
        assert {:id "id13"} defass#y#0;
        return;
    }

    assert {:id "id14"} defass#y#0;
}

id13. So maybe is really a bug in dafny in mapping back and fort from boogie to z3


# Problemas Passos
- Parece ser mesmo problema do mapping boogie -> dafny (terei que fazer debug)
- Posso tmb correr paper da CAB extracao de lurking axioms no z3 (apartir do bogey) que posteriormente terei que usar isso certamente (talvez fazer este ponto primeiro!)