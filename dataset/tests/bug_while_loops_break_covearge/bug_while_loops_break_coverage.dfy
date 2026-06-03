method bugTest(n: int) returns (count: int)
  requires n > 177
  ensures count >= 18542 
{
  count := 18542; 
  var i := 12;
  while (i  <= n)
    invariant count >= 18542
  {
    count := count + 35;
    i := i + 23;
  }
}

//::: Name - While loops that done taffect anything break coverage tracking completly
//::: To see this tested why was found you must see L5 and uncomment that line (it appears on the core of assertion on line 9)
//::: I think it is because of the bug
//::: L5 - CovTest
//::: L5 - CovComplete