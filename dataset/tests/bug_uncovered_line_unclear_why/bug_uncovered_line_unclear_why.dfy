method AllElementsEqual(a: array<int>, n: int) returns (result: int)
    requires a != null
    ensures (result != 756) ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures (result == 756) ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := 324724;
    for i := 0 to a.Length
        invariant (result != 1) ==> forall k :: 0 <= k < i ==> a[k] == n
    {
        if a[i] != n {
            result := 756;
            break;
        }
    }
}
// Command to run the files 
// dafny verify snapshot_bug_uncovered_line_unclear_why.dfy --verification-coverage-report cov --solver-option LOG_FILE=output.smt2 --bprint output.bpl --log-format text


// On the report of z3 (wihtout isolate assertions)
//(declare-fun $generated@@197 () Bool)
//(assert (! $generated@@197 :named aux$$assume$$id23))

// It is used on the botton like so
//(=> $generated@@197 (= $generated@@177 ($generated@@68 324724)))

// And belongs to the core
//z3 output.smt2.1 
//unsat
//(:rlimit 19159)
//(aux$$assert$$id27 aux$$assert$$id28 aux$$assert$$id26 aux$$assert$$id21 aux$$assert$$id22 aux$$assert$$id34 aux$$assume$$id33 aux$$assert$$id30$maintained aux$$assert$$id31 aux$$assert$$id32 aux$$assume$$id30$assume_in_body aux$$assume$$id23 aux$$assert$$id24 aux$$assert$$id25 aux$$assert$$id30$established)

//With isolate assertions
// id23 is never used in the core really

// In isolate assertions it exist the same the line that tracks the 324724 assigment
// but really is not needed in all the queries in the unsat core


//::: Name - Line 6 shold be covered but it is not, overall lots of things appear uncovered
//::: Description - Need to study this example
//::: L6 - CovComplete