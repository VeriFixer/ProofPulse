method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if(x == 0){
    y := 0; // Unused by proof  _USECASE_find_irrelevant_lines.dfy(6,5)-(6,11): assignment (or return)
  }

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}