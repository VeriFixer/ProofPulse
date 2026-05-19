method Max(a: int, b: int) returns (max: int)
    ensures max >= a && max >= b
    ensures max == a || max == b
{
    if a >= b {
        max := a;
    } else {
        max := b;
    }
}

//::: Name - Direct assignment branching should produce coverage
//::: Description - if/else with direct assignments produces no proof trace; all lines appear Uncovered when they should be CovComplete
//::: L2 - CovComplete
//::: L3 - CovComplete
//::: L6 - CovComplete
//::: L8 - CovComplete
