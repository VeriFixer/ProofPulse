method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  assert(43 == 43); // To catch this being useless it is necessary to check only the dependency related to postconditions
                    // This would catch this assertion as being useless

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}

//:: Someimes when there are two equal asserrtions or really equivalent the assertion is removed from proof core
//:: See gaussian example
//:: From proof dependency see if assertions is related to any postcondition in any way
//:: Inside loops assertions have to be also related with the invariants assertions

