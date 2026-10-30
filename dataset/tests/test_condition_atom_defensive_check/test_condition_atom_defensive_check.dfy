method Div(a: int, b: int) returns (q: int)
  requires b > 0
  ensures q == a / b
{
  if b != 0 {
    q := a / b;
  } else {
    q := 0;
  }
}

//::: Name - Defensive condition implied by the precondition
//::: Description - The atom is covered: if it could be false the else branch would break the postcondition. The dead branch itself is uncovered code
//::: L5 - CovComplete
//::: L8 - Uncovered
