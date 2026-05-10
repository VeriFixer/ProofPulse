function IdDemo<T>(a: T): T {
  a
}

method DemoRedundantLine(x: int) returns (y: int)
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
{
  if x == 0 {
    y := 0; 
  }

  if x < 0 {
    y := -x ;
  } else {
    y := IdDemo(x);
  }
}

method DemoNoContracts(x: int) returns (y: int)
{
  var tmp := x + 2;
  y := tmp - 1;
}

method DemoSpecNotUsingCode(x: int) returns (y: int)
  ensures 4 == 4
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
{
  if x < 0 {
    y := -x;
  } else {
    y := IdDemo(x);
  }
}

method DemoIrrelevantAssertion(x: int) returns (y: int)
  ensures y == x
{
  assert 43 == 43;
  y := IdDemo(x);
}

method ProducerNonNegative(x: int) returns (y: int)
  ensures y >= 0
{
  if x < 0 {
    y := 0;
  } else {
    y := IdDemo(x);
  }
}

method DemoUnusedContractAtCallSite_IndependentProof()
{
  var t := ProducerNonNegative(-100);
  assert 1 + 1 == 2;
}