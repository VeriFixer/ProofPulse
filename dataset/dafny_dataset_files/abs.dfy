method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

//:: Expected: All Covered

//::: Expected all covered but boogey->SMT does not create
//::: an assume statement for y:=x not being possible to
//::: capture the named assumption in the proof core 
//::: ticket opened https://github.com/boogie-org/boogie/issues/1066

//:: Outcome:
//:: Dafny program verifier finished with 1 verified, 0 errors
// Results for Abs (correctness)
//   Overall outcome: Correct
//   Overall time: 00:00:00.0970232
//   Overall resource count: 4446
//   Maximum assertion batch time: 00:00:00.0970232
//   Maximum assertion batch resource count: 4446
//   Assertion batch 1:
//     Outcome: Valid
//     Duration: 00:00:00.0970232
//     Resource count: 4446
//     Assertions:
//       abs.dfy(10,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
//       abs.dfy(2,21): this postcondition holds
//       abs.dfy(3,22): this postcondition holds
//     Proof dependencies:
//       abs.dfy(2,20)-(2,23): ensures clause
//       abs.dfy(3,19)-(3,24): ensures clause
//       abs.dfy(6,5)-(6,12): assignment (or return)
//       abs.dfy(10,1)-(10,1): out-parameter 'y', which is subject to definite-assignment rules, is always initialized at this return point
//     Unused by proof:
//       abs.dfy(8,5)-(8,11): assignment (or return)

