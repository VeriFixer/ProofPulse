method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{
  min := s[0];
  for i := 1 to s.Length
    invariant forall k :: 0 <= k < i ==> min <= s[k]
    invariant exists k :: 0 <= k < i && min == s[k]
  {
    if s[i] < min
    {
      min := s[i];
    }
  }
}

//::: Name - Tests that the propagation is well made on forall elemnts as covered
//::: Description - Line 14 should be covered
//::: L13 - CovComplete
