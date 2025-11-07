method Abs(x: int) returns (y: int)
{
  if x < 0 {
    y := -x; // _USECASE_no_postconditions.dfy(4,5)-(4,12): assignment (or return)
  } else {
    y := Id(x); // _USECASE_no_postconditions.dfy(6,5)-(6,11): assignment (or return)
  }
} //Note: As this is the only assertion that is added automatically it is really covered (in other tests with postcondiiton this assertion does not run)

function Id<T> (a : T) : T {
    a
}

//::: Name - No postcondition
//::: Description - Code lines should appear uncovered
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovComplete
//::: L4 - Uncovered
//::: L5 - CovComplete
//::: L6 - Uncovered
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12- CovComplete
