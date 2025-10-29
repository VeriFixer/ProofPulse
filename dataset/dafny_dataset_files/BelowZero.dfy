/* 
HumanEvalX 3
You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. 
Your task is to detect if at any point the balance of account falls below zero, and at that point function 
should return True. Otherwise it should return False.
*/

function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
    if i == 0 {
        // sum(s,0) = 0 and sum(s,1) = s[0] + sum(s[1..],0) = s[0]
        assert sum(s, 0) == 0;
        assert sum(s, 1) == s[0] + sum(s[1..], 0);
        assert sum(s, 0) + s[0] == sum(s, 1);
    } else {
        sum_plus(s[1..], i - 1);
    }
}

method BelowZero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    for i := 0 to |ops|
        invariant t == sum(ops, i)
        invariant forall n: nat :: n <= i ==> sum(ops, n) >= 0
    {
        t := t + ops[i];
        //::: Outcome this line is not covered but should
        // No bogey a call ao sum_plus nao parece estar a ser coberto mas ainda nao percebi porque de todo
        // Mas vamos para outro
        //assert {:id "id88"} $Is(i#0, Tclass._System.nat());
        //i##0_0 := i#0;
        //call {:id "id89"} Call$$_module.__default.sum__plus(s##0_0, i##0_0);
       
        // Ou esta
        //assert {:id "id56"} 0 <= i#0 || Seq#Rank(s##1_0) < Seq#Rank(s#0) || i##1_0 == i#0;
        //assert {:id "id57"} Seq#Rank(s##1_0) < Seq#Rank(s#0)
        //   || (Seq#Rank(s##1_0) == Seq#Rank(s#0) && i##1_0 < i#0);
        //call {:id "id58"} Call$$_module.__default.sum__plus(s##1_0, i##1_0);
        // TrCallStmt: After ProcessCallStmt
        sum_plus(ops, i);  //BelowZero.dfy(50,9)-(50,25): call (unused but obviouly needed!)
        //:::
        if t < 0 {
            result := true;
            return;
        }
    }
}