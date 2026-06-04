method ret32(a: int) returns (x:int)
    ensures x==32 
    requires a <10
{
    x := 32;
}
method Main() {
	var n := ret32(5);
    assert n==32;
}


// Actually line 8 is expected CovComplete that it is what is recevign, this is not buging out as this behaviour is being ignored
// Changed to uncovered hust for bug test to pass (it must give an error)






// With calld this is always happening
//  Results for Main (correctness)
//   Overall outcome: Correct
//   Overall time: 00:00:00.0572679
//   Overall resource count: 4352
//   Maximum assertion batch time: 00:00:00.0572679
//   Maximum assertion batch resource count: 4352
//   Assertion batch 1:
//     Outcome: Valid
//     Duration: 00:00:00.0572679
//     Resource count: 4352
//     Assertions:
//       _main_method_that_calls.dfy(10,13): assertion always holds
//     Proof dependencies:
//       _main_method_that_calls.dfy(9,8)-(9,18): ensures clause at _main_method_that_calls.dfy(2,13)-(2,16) from call
//       _main_method_that_calls.dfy(10,5)-(10,17): assertion always holds
//     Unused by proof:
//       _main_method_that_calls.dfy(9,8)-(9,18): call
//       _main_method_that_calls.dfy(9,8)-(9,18): assignment (or return)

// Calls to function methods appear always unused (but here clearly the condiitons were used)
// // Boogie creates this
// implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Main (correctness)"} Impl$$_module.__default.Main() returns ($_reverifyPost: bool)
// {
//   var $_ModifiesFrame: [ref,Field]bool;
//   var n#0: int;
//   var $rhs##0: int;
//     // AddMethodImpl: Main, Impl$$_module.__default.Main
//     $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
//       $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
//     assume {:captureState "_main_method_that_calls.dfy(8,14): initial state"} true;
//     $_reverifyPost := false;
//     // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/_main_method_that_calls.dfy(9,11)
//     assume true;
//     // TrCallStmt: Adding lhs with type int
//     // TrCallStmt: Before ProcessCallStmt
//     call {:id "id5"} $rhs##0 := Call$$_module.__default.ret32();
//     // TrCallStmt: After ProcessCallStmt
//     n#0 := $rhs##0;
//     assume {:captureState "_main_method_that_calls.dfy(9,17)"} true;
//     // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/_main_method_that_calls.dfy(10,5)
//     assume true;
//     assert {:id "id7"} n#0 == LitInt(32);
// }

// SMT
// (assert (! $generated@@102 :named aux$$assume$$id1$id5$ensures))
// (=> $generated@@102 (= $generated@@103 ($generated@@46 32)))
// (declare-fun $generated@@103 () Int)
// (declare-fun $generated@@46 (Int) Int)
// (assert (forall (($generated@@47 Int) ) (! (= ($generated@@46 $generated@@47) $generated@@47)
//  :pattern ( ($generated@@46 $generated@@47))
//  (assert (forall (($generated@@93 Int) ) (! (= ($generated@@51 $generated@@10 ($generated@@13 ($generated@@46 $generated@@93))) ($generated@@48 $generated@@2 ($generated@@51 $generated@@10 ($generated@@13 $generated@@93))))
//  :pattern ( ($generated@@51 $generated@@10 ($generated@@13 ($generated@@46 $generated@@93))))
// unsat cores
//(aux$$assume$$id1$id5$ensures aux$$assert$$id7)
// z3 generates two files
// smt2 unsat cores are
// (aux$$assume$$id3 aux$$assert$$id4 aux$$assert$$id2)
// smt2.1 unstat core are 
//(aux$$assume$$id1$id5$ensures aux$$assert$$id7)
// Ret 32 call has some ingo here
// procedure {:verboseName "ret32 (call)"} Call$$_module.__default.ret32() returns (x#0: int);
//   modifies $Heap;
//   // user-defined postconditions
//   free ensures true;
//   ensures {:id "id1"} x#0 == LitInt(32);
//   // frame condition: object granularity
//   free ensures (forall $o: ref :: 
//     { $Heap[$o] } 
//     $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
//        ==> $Heap[$o] == old($Heap)[$o]);
//   // boilerplate
//   free ensures $HeapSucc(old($Heap), $Heap);
// I beleive that by the encoding smt was transated both assertion into one
// implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Main (correctness)"} Impl$$_module.__default.Main() returns ($_reverifyPost: bool)
// {
//   var $_ModifiesFrame: [ref,Field]bool;
//   var n#0: int;
//   var $rhs##0: int;
//     // AddMethodImpl: Main, Impl$$_module.__default.Main
//     $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
//       $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
//     assume {:captureState "_main_method_that_calls.dfy(8,14): initial state"} true;
//     $_reverifyPost := false;
//     // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/_main_method_that_calls.dfy(9,11)
//     assume true;
//     // TrCallStmt: Adding lhs with type int
//     // TrCallStmt: Before ProcessCallStmt
//     call {:id "id5"} $rhs##0 := Call$$_module.__default.ret32();
//     // TrCallStmt: After ProcessCallStmt
//     n#0 := $rhs##0;
//     assume {:captureState "_main_method_that_calls.dfy(9,17)"} true;
//     // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/_main_method_that_calls.dfy(10,5)
//     assume true;
//     assert {:id "id7"} n#0 == LitInt(32);
// }
// id 5 and id 1 were merged in 
// aux$$assume$$id1$id5$ensures
// Therefore the assertion individually was bugged and thought as not be used.
// This in ret32 call
// // procedure {:verboseName "ret32 (call)"} Call$$_module.__default.ret32() returns (x#0: int);
//   modifies $Heap;
//   // user-defined postconditions
//   free ensures true;
//   ensures {:id "id1"} x#0 == LitInt(32);
// And the assigment:
//     call {:id "id5"} $rhs##0 := Call$$_module.__default.ret32();
// Bug Boogie->Dafnt passage, or z3 to bogie. Boogie did not consider id1 and id5 covered even though
// The assertion created by both in z3 aux$$assume$$id1$id5$ensures was covered
//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_method_call.dfy|ret32|correctness|2,13-2,16
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 16
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3492
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_method_call.dfy|ret32|correctness|5,5-5,12
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 12
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_method_call.dfy|ret32|correctness|3,14-3,17
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 3
//::       col: 14
//::     end:
//::       line: 3
//::       col: 17
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_method_call.dfy|ret32|correctness|6,1-6,1
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
//::       col: 1
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'x', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_method_call.dfy|Main|correctness|8,6-8,19
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 8
//::       col: 6
//::     end:
//::       line: 8
//::       col: 19
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - the precondition always holds
//::       - requires clause at snapshot_test_method_call.dfy(3,14)-(3,17) from call
//::       - call
//::       - assignment (or return)
//::       - assignment (or return)
//::       - ensures clause at snapshot_test_method_call.dfy(2,13)-(2,16) from call
//::       - call
//::     roles:
//::       isTop: true
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3354
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_method_call.dfy|Main|correctness|3,14-3,17
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 3
//::       col: 14
//::     end:
//::       line: 3
//::       col: 17
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_method_call.dfy|Main|correctness|9,5-9,17
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 17
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionManual
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 4634
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_method_call.dfy|Main|correctness|2,13-2,16
//::     file: snapshot_test_method_call.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 16
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_method_call.dfy|ret32|correctness|2,13-2,16
//::       provers:
//::         - snapshot_test_method_call.dfy|ret32|correctness|5,5-5,12
//::     - top: snapshot_test_method_call.dfy|Main|correctness|9,5-9,17
//::       provers:
//::         - snapshot_test_method_call.dfy|Main|correctness|8,6-8,19
//::   proofUnused:
//::     - top: snapshot_test_method_call.dfy|ret32|correctness|2,13-2,16
//::       unused:
//::         - snapshot_test_method_call.dfy|ret32|correctness|3,14-3,17
//::         - snapshot_test_method_call.dfy|ret32|correctness|6,1-6,1
//::     - top: snapshot_test_method_call.dfy|Main|correctness|8,6-8,19
//::       unused:
//::         - snapshot_test_method_call.dfy|Main|correctness|8,6-8,19
//::         - snapshot_test_method_call.dfy|Main|correctness|9,5-9,17
//::     - top: snapshot_test_method_call.dfy|Main|correctness|9,5-9,17
//::       unused:
//::         - snapshot_test_method_call.dfy|Main|correctness|8,6-8,19
//::   connections:
//::     - call: snapshot_test_method_call.dfy|Main|correctness|8,6-8,19
//::       targets:
//::         - snapshot_test_method_call.dfy|Main|correctness|3,14-3,17
//::         - snapshot_test_method_call.dfy|Main|correctness|2,13-2,16
//::
