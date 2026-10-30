function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

method SumThree(s: seq<int>) returns (r: int)
  requires |s| == 3
  ensures r == Sum(s)
{
  r := s[0] + s[1] + s[2];
  assert (Sum(s[2..]) == s[2] && Sum(s[1..]) == s[1] + Sum(s[2..]));
}

//::: Name - Assert split into conjuncts, used by a postcondition
//::: Description - Dafny checks each conjunct as its own assertion but reports the use as one assert statement over the whole expression; both conjuncts must be covered (removing the assert breaks the postcondition)
//::: L11 - CovComplete
