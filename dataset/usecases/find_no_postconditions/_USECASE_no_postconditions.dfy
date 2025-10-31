method Abs(x: int) returns (y: int)
{
  if x < 0 {
    y := -x; // _USECASE_no_postconditions.dfy(4,5)-(4,12): assignment (or return)
  } else {
    y := Id(x); // _USECASE_no_postconditions.dfy(6,5)-(6,11): assignment (or return)

  }
}

function Id<T> (a : T) : T {
    a
}