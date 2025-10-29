function id(x:int) : int {
  x
}

method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
{
  //  array_append.dfy(12,3)-(12,27): assignment (or return)
  // Cannot understand why this is failing will need to debug

  // I serriously believe that the problem is this:
  // In Boogie
  //   assume true;
  // assert {:id "id8"} a#0 != null;
  // assume true;
  // assert {:id "id9"} 0 <= _System.array.Length(a#0) + 1;
  // havoc $nw;
  // assume $nw != null && $Is($nw, Tclass._System.array?(TInt));
  // assume !$Unbox(read($Heap, $nw, alloc)): bool;
  // assume _System.array.Length($nw) == _System.array.Length(a#0) + 1;
  // $Heap := update($Heap, $nw, alloc, $Box(true));
  // assume $IsGoodHeap($Heap);
  // assume $IsHeapAnchor($Heap);
  // c#0 := $nw;  (this assigment is not being tranlated as an assume)
  //              (and it is not captured, same problem I figured it out but more internal)
  //              (Unfortunatlye it seems that this has to be handle really on boogie no id call to save us
  // defass#c#0 := true;
  // assume {:captureState "array_append.dfy(10,26)"} true;

  // Not 100% debug the SMT is too much difficult as it is but highly certain
  // Need a way from boogie to generate SMT (to have the freedom to modify boogie itself)

  c := new int[a.Length+1];
  var d := 123121515;
  var i:= 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    // Identifed problem, it is lurking axiom almost for sure
    invariant forall ii::0<=ii<i ==> c[ii]==a[ii]
  {
    c[i] := a[i];
    i:=i+1;
  }
  // identity needed or proof dependency of assigment is erased
  c[a.Length]:=id(b);
}

//::: Expected: All Covered

// Outcome
// Dafny program verifier finished with 2 verified, 0 errors

// Results for append (well-formedness)
//   Overall outcome: Correct
//   Overall time: 00:00:00.1385340
//   Overall resource count: 12981
//   Maximum assertion batch time: 00:00:00.1385340
//   Maximum assertion batch resource count: 12981

//   Assertion batch 1:
//     Outcome: Valid
//     Duration: 00:00:00.1385340
//     Resource count: 12981

//     Assertions:
//       Clover_array_append.dfy(2,12): array is never null
//       Clover_array_append.dfy(2,27): array is never null

//     Proof dependencies:
//       Clover_array_append.dfy(2,12)-(2,12): array is never null
//       Clover_array_append.dfy(2,27)-(2,27): array is never null

//     Unused by proof:
//       Clover_array_append.dfy(2,12)-(2,31): method ensures clause

// Results for append (correctness)
//   Overall outcome: Correct
//   Overall time: 00:00:00.1524638
//   Overall resource count: 55626
//   Maximum assertion batch time: 00:00:00.1524638
//   Maximum assertion batch resource count: 55626

//   Assertion batch 1:
//     Outcome: Valid
//     Duration: 00:00:00.1524638
//     Resource count: 55626

//     Assertions:
//       Clover_array_append.dfy(4,18): target object is never null
//       Clover_array_append.dfy(4,24): array size is never negative
//       Clover_array_append.dfy(7,17): this loop invariant holds on entry
//       Clover_array_append.dfy(7,22): this loop invariant holds on entry
//       Clover_array_append.dfy(8,15): this loop invariant holds on entry
//       Clover_array_append.dfy(6,16): target object is never null
//       Clover_array_append.dfy(10,5): variable 'c', which is subject to definite-assignment rules, is always initialized here
//       Clover_array_append.dfy(10,5): array is never null
//       Clover_array_append.dfy(10,6): index in range
//       Clover_array_append.dfy(10,6): an array element is in the enclosing context's modifies clause
//       Clover_array_append.dfy(10,13): array is never null
//       Clover_array_append.dfy(10,14): index in range
//       Clover_array_append.dfy(6,16): decreases expression is bounded below by 0
//       Clover_array_append.dfy(6,3): loop or recursion terminates
//       Clover_array_append.dfy(7,17): this loop invariant is maintained by the loop
//       Clover_array_append.dfy(7,22): this loop invariant is maintained by the loop
//       Clover_array_append.dfy(8,15): this loop invariant is maintained by the loop
//       Clover_array_append.dfy(13,3): variable 'c', which is subject to definite-assignment rules, is always initialized here
//       Clover_array_append.dfy(13,3): array is never null
//       Clover_array_append.dfy(13,7): target object is never null
//       Clover_array_append.dfy(13,4): index in range
//       Clover_array_append.dfy(13,4): an array element is in the enclosing context's modifies clause
//       Clover_array_append.dfy(14,1): out-parameter 'c', which is subject to definite-assignment rules, is always initialized at this return point
//       Clover_array_append.dfy(2,24): this postcondition holds
//       Clover_array_append.dfy(6,16): target object is never null
//       Clover_array_append.dfy(8,38): variable 'c', which is subject to definite-assignment rules, is always initialized here
//       Clover_array_append.dfy(8,38): array is never null
//       Clover_array_append.dfy(8,39): index in range
//       Clover_array_append.dfy(8,45): array is never null
//       Clover_array_append.dfy(8,46): index in range
//       Clover_array_append.dfy(7,27): target object is never null

//     Proof dependencies:
//       Clover_array_append.dfy(2,12)-(2,31): ensures clause
//       Clover_array_append.dfy(4,16)-(4,18): target object is never null
//       Clover_array_append.dfy(4,16)-(4,25): array size is never negative
//       Clover_array_append.dfy(5,7)-(5,12): assignment (or return)
//       Clover_array_append.dfy(6,3)-(12,3): loop or recursion terminates
//       Clover_array_append.dfy(6,14)-(6,16): decreases expression is bounded below by 0
//       Clover_array_append.dfy(6,14)-(6,16): target object is never null
//       Clover_array_append.dfy(6,14)-(6,16): target object is never null
//       Clover_array_append.dfy(7,15)-(7,20): loop invariant always holds
//       Clover_array_append.dfy(7,15)-(7,20): loop invariant always holds
//       Clover_array_append.dfy(7,15)-(7,27): loop invariant
//       Clover_array_append.dfy(7,20)-(7,27): loop invariant always holds
//       Clover_array_append.dfy(7,20)-(7,27): loop invariant always holds
//       Clover_array_append.dfy(7,20)-(7,27): loop invariant always holds
//       Clover_array_append.dfy(7,25)-(7,27): target object is never null
//       Clover_array_append.dfy(8,15)-(8,49): loop invariant always holds
//       Clover_array_append.dfy(8,15)-(8,49): loop invariant always holds
//       Clover_array_append.dfy(8,15)-(8,49): loop invariant always holds
//       Clover_array_append.dfy(8,38)-(8,38): array is never null
//       Clover_array_append.dfy(8,38)-(8,38): variable 'c', which is subject to definite-assignment rules, is always initialized here
//       Clover_array_append.dfy(8,38)-(8,42): index in range
//       Clover_array_append.dfy(8,45)-(8,45): array is never null
//       Clover_array_append.dfy(8,45)-(8,49): index in range
//       Clover_array_append.dfy(10,5)-(10,5): array is never null
//       Clover_array_append.dfy(10,5)-(10,5): variable 'c', which is subject to definite-assignment rules, is always initialized here
//       Clover_array_append.dfy(10,5)-(10,8): an array element is in the enclosing context's modifies clause
//       Clover_array_append.dfy(10,5)-(10,8): index in range
//       Clover_array_append.dfy(10,5)-(10,17): assignment (or return)
//       Clover_array_append.dfy(10,5)-(10,17): assignment (or return)
//       Clover_array_append.dfy(10,13)-(10,13): array is never null
//       Clover_array_append.dfy(10,13)-(10,16): index in range
//       Clover_array_append.dfy(11,5)-(11,11): assignment (or return)
//       Clover_array_append.dfy(13,3)-(13,3): array is never null
//       Clover_array_append.dfy(13,3)-(13,3): variable 'c', which is subject to definite-assignment rules, is always initialized here
//       Clover_array_append.dfy(13,3)-(13,13): an array element is in the enclosing context's modifies clause
//       Clover_array_append.dfy(13,3)-(13,13): index in range
//       Clover_array_append.dfy(13,3)-(13,17): assignment (or return)
//       Clover_array_append.dfy(13,5)-(13,7): target object is never null
//       Clover_array_append.dfy(14,1)-(14,1): out-parameter 'c', which is subject to definite-assignment rules, is always initialized at this return point
//     Unused by proof:
//       Clover_array_append.dfy(4,3)-(4,27): assignment (or return) // Explanation of this given on top I beleice
//       Clover_array_append.dfy(8,15)-(8,49): loop invariant // Identifed something with lurking possiblt
//       Clover_array_append.dfy(13,3)-(13,17): assignment (or return) // Soved with id() call


// Assume in Boogey that was not used!
//           assume {:id "id21"} (forall ii#1: int :: 
//              { read($Heap, a#0, IndexField(ii#1)) } { read($Heap, c#0, IndexField(ii#1)) } 
//              LitInt(0) <= ii#1 && ii#1 < i#0
//                 ==> $Unbox(read($Heap, c#0, IndexField(ii#1))): int
//                   == $Unbox(read($Heap, a#0, IndexField(ii#1))): int);
// Fix this are lurking axioms for sure
//:::