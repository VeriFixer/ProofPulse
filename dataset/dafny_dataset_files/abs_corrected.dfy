function id(x:int) : int {
  x
}

method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x;
  } else {
    y := id(x);
  }
}

//:: Expected: All Covered

//:: Outcome:
// Dafny program verifier finished with 1 verified, 0 errors
// Results for Abs (correctness)
//   Overall outcome: Correct
//   Overall time: 00:00:00.1219035
//   Overall resource count: 5337
//   Maximum assertion batch time: 00:00:00.1219035
//   Maximum assertion batch resource count: 5337
//   Assertion batch 1:
//     Outcome: Valid
//     Duration: 00:00:00.1219035
//     Resource count: 5337
//     Assertions:
//       abs_corrected.dfy(14,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
//       abs_corrected.dfy(6,21): this postcondition holds
//       abs_corrected.dfy(7,22): this postcondition holds
//     Proof dependencies:
//       abs_corrected.dfy(1,1)-(3,1): function definition for id
//       abs_corrected.dfy(6,20)-(6,23): ensures clause
//       abs_corrected.dfy(7,19)-(7,24): ensures clause
//       abs_corrected.dfy(10,5)-(10,12): assignment (or return)
//       abs_corrected.dfy(12,5)-(12,15): assignment (or return)
//       abs_corrected.dfy(14,1)-(14,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
//     Unused by proof:

