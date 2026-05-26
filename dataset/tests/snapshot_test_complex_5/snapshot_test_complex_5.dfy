// Redo for exam

function gcd(a: nat, b: nat): nat

lemma r1(a: nat)
    ensures gcd(a, 0) == a

lemma r2(a:nat)
    ensures gcd(a, a) == a

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
    decreases b
{
    if a < b {
        r3(a,b);
        r := GCD1(b, a);
    } else if (a % b == 0) {
        r4(a,b);
        assert b > 0;
        assert gcd(a, b) == gcd(b, a % b);
        assert a % b == 0;
        assert gcd(a, b) == gcd(b, 0);
        r1(b);
        assert gcd(a, b) == b;
        r := b;
        assert gcd(a,b) == r;
    } else {
        r4(a,b);
        r := GCD1(b, a % b);
        assert gcd(a,b) == r;
    }
    assert gcd(a,b) == r;
}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    decreases b
    ensures gcd(a,b) == r
{
    r1(a);
    r4(a,b);
    assert
        ( b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a) )
        &&
        ( (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b))) );
    assert
        b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a);
    assert
        b == 0 ==> a > 0 && b >= 0 && gcd(a,b) == a;
    assert
        (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b)));
    assert
        b >= 0 && b != 0 ==> b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
    if b == 0 {
        r1(a);
        assert
            gcd(a,b) == a;
        r := a;
        assert
            gcd(a,b) == r;
    } else {
        r4(a,b);
        // Method call rule
        assert
            b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
        // assert
        //    gcd(a,b) == GCD2(b, a % b);
        r := GCD2(b, a % b);
        assert
            gcd(a,b) == r;
    }
    assert
        gcd(a,b) == r;
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_complex_5.dfy|r1|well-formedness|6,20-6,20|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 6
//::       col: 20
//::     end:
//::       line: 6
//::       col: 20
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: r1
//::     methodType: well-formedness
//::     assertionGroup: r1
//::   - id: snapshot_test_complex_5.dfy|r1|well-formedness|6,13-6,26|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 6
//::       col: 13
//::     end:
//::       line: 6
//::       col: 26
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: r1
//::     methodType: well-formedness
//::     assertionGroup: r1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|r4|well-formedness|15,45-15,45|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 45
//::     end:
//::       line: 15
//::       col: 45
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: r4
//::     methodType: well-formedness
//::     assertionGroup: r4
//::   - id: snapshot_test_complex_5.dfy|r4|well-formedness|15,13-15,17|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 13
//::     end:
//::       line: 15
//::       col: 17
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: r4
//::     methodType: well-formedness
//::     assertionGroup: r4
//::   - id: snapshot_test_complex_5.dfy|r4|well-formedness|15,43-15,47|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 43
//::     end:
//::       line: 15
//::       col: 47
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: r4
//::     methodType: well-formedness
//::     assertionGroup: r4
//::   - id: >-
//::       snapshot_test_complex_5.dfy|r4|well-formedness|15,43-15,47|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 43
//::     end:
//::       line: 15
//::       col: 47
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: r4
//::     methodType: well-formedness
//::     assertionGroup: r4
//::   - id: snapshot_test_complex_5.dfy|r4|well-formedness|15,23-15,48|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 23
//::     end:
//::       line: 15
//::       col: 48
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: r4
//::     methodType: well-formedness
//::     assertionGroup: r4
//::   - id: snapshot_test_complex_5.dfy|r4|well-formedness|15,13-15,48|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 13
//::     end:
//::       line: 15
//::       col: 48
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: r4
//::     methodType: well-formedness
//::     assertionGroup: r4
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|well-formedness|19,17-19,17|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 19
//::       col: 17
//::     end:
//::       line: 19
//::       col: 17
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: well-formedness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|well-formedness|18,14-18,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 18
//::       col: 14
//::     end:
//::       line: 18
//::       col: 18
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: well-formedness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|well-formedness|18,23-18,27|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 18
//::       col: 23
//::     end:
//::       line: 18
//::       col: 27
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: well-formedness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|well-formedness|19,19-19,19|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 19
//::       col: 19
//::     end:
//::       line: 19
//::       col: 19
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: well-formedness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|well-formedness|19,13-19,25|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 19
//::       col: 13
//::     end:
//::       line: 19
//::       col: 25
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: well-formedness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|25,18-25,18|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 25
//::       col: 18
//::     end:
//::       line: 25
//::       col: 18
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 18
//::       col: 23
//::     end:
//::       line: 18
//::       col: 27
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 25
//::       col: 16
//::     end:
//::       line: 25
//::       col: 20
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 18
//::       col: 14
//::     end:
//::       line: 18
//::       col: 18
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 19
//::       col: 13
//::     end:
//::       line: 19
//::       col: 25
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 23
//::       col: 12
//::     end:
//::       line: 23
//::       col: 12
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 23
//::       col: 14
//::     end:
//::       line: 23
//::       col: 14
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 23
//::       col: 9
//::     end:
//::       line: 23
//::       col: 16
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 24
//::       col: 9
//::     end:
//::       line: 24
//::       col: 24
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 24
//::       col: 9
//::     end:
//::       line: 24
//::       col: 24
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 26
//::       col: 12
//::     end:
//::       line: 26
//::       col: 12
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 26
//::       col: 14
//::     end:
//::       line: 26
//::       col: 14
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 26
//::       col: 9
//::     end:
//::       line: 26
//::       col: 16
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 27
//::       col: 9
//::     end:
//::       line: 27
//::       col: 21
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 20
//::     end:
//::       line: 28
//::       col: 20
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 23
//::     end:
//::       line: 28
//::       col: 23
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 33
//::     end:
//::       line: 28
//::       col: 33
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 36
//::     end:
//::       line: 28
//::       col: 40
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 36
//::     end:
//::       line: 28
//::       col: 40
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 9
//::     end:
//::       line: 28
//::       col: 42
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 29
//::       col: 16
//::     end:
//::       line: 29
//::       col: 20
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 29
//::       col: 9
//::     end:
//::       line: 29
//::       col: 26
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 30
//::       col: 20
//::     end:
//::       line: 30
//::       col: 20
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 30
//::       col: 23
//::     end:
//::       line: 30
//::       col: 23
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 30
//::       col: 33
//::     end:
//::       line: 30
//::       col: 33
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 30
//::       col: 36
//::     end:
//::       line: 30
//::       col: 36
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 30
//::       col: 9
//::     end:
//::       line: 30
//::       col: 38
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 31
//::       col: 12
//::     end:
//::       line: 31
//::       col: 12
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 31
//::       col: 9
//::     end:
//::       line: 31
//::       col: 14
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 32
//::       col: 20
//::     end:
//::       line: 32
//::       col: 20
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 32
//::       col: 23
//::     end:
//::       line: 32
//::       col: 23
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 32
//::       col: 9
//::     end:
//::       line: 32
//::       col: 30
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 33
//::       col: 9
//::     end:
//::       line: 33
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 34
//::       col: 20
//::     end:
//::       line: 34
//::       col: 20
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 34
//::       col: 22
//::     end:
//::       line: 34
//::       col: 22
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 34
//::       col: 28
//::     end:
//::       line: 34
//::       col: 28
//::     prooftext: >-
//::       variable 'r', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 34
//::       col: 9
//::     end:
//::       line: 34
//::       col: 29
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 36
//::       col: 12
//::     end:
//::       line: 36
//::       col: 12
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 36
//::       col: 14
//::     end:
//::       line: 36
//::       col: 14
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 36
//::       col: 9
//::     end:
//::       line: 36
//::       col: 16
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 22
//::     end:
//::       line: 37
//::       col: 26
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 9
//::     end:
//::       line: 37
//::       col: 28
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 9
//::     end:
//::       line: 37
//::       col: 28
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 38
//::       col: 20
//::     end:
//::       line: 38
//::       col: 20
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 38
//::       col: 22
//::     end:
//::       line: 38
//::       col: 22
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 38
//::       col: 28
//::     end:
//::       line: 38
//::       col: 28
//::     prooftext: >-
//::       variable 'r', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 38
//::       col: 9
//::     end:
//::       line: 38
//::       col: 29
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 40
//::       col: 16
//::     end:
//::       line: 40
//::       col: 16
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 40
//::       col: 18
//::     end:
//::       line: 40
//::       col: 18
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 40
//::       col: 24
//::     end:
//::       line: 40
//::       col: 24
//::     prooftext: >-
//::       variable 'r', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 40
//::       col: 5
//::     end:
//::       line: 40
//::       col: 25
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 41
//::       col: 1
//::     end:
//::       line: 41
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'r', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|37,24-37,24|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 24
//::     end:
//::       line: 37
//::       col: 24
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|37,18-37,18|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 18
//::     end:
//::       line: 37
//::       col: 18
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,18-37,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 18
//::     end:
//::       line: 37
//::       col: 18
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 37
//::       col: 9
//::     end:
//::       line: 37
//::       col: 28
//::     prooftext: requires clause at snapshot_test_complex_5.dfy(18,14)-(18,18) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 38
//::       col: 9
//::     end:
//::       line: 38
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 36
//::       col: 9
//::     end:
//::       line: 36
//::       col: 16
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(15,23)-(15,48) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|15,23-15,48|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 23
//::     end:
//::       line: 15
//::       col: 48
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,5|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 40
//::       col: 5
//::     end:
//::       line: 40
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 23
//::       col: 9
//::     end:
//::       line: 23
//::       col: 16
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(12,13)-(12,34) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|12,13-12,34|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 12
//::       col: 13
//::     end:
//::       line: 12
//::       col: 34
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 24
//::       col: 9
//::     end:
//::       line: 24
//::       col: 24
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(19,13)-(19,25) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|19,22-19,22|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 19
//::       col: 22
//::     end:
//::       line: 19
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 27
//::       col: 9
//::     end:
//::       line: 27
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|28,38-28,38|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 38
//::     end:
//::       line: 28
//::       col: 38
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 28
//::       col: 9
//::     end:
//::       line: 28
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 26
//::       col: 9
//::     end:
//::       line: 26
//::       col: 16
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(15,23)-(15,48) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|29,18-29,18|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 29
//::       col: 18
//::     end:
//::       line: 29
//::       col: 18
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 29
//::       col: 9
//::     end:
//::       line: 29
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 30
//::       col: 9
//::     end:
//::       line: 30
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 32
//::       col: 9
//::     end:
//::       line: 32
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 31
//::       col: 9
//::     end:
//::       line: 31
//::       col: 14
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(6,13)-(6,26) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|6,13-6,26|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 6
//::       col: 13
//::     end:
//::       line: 6
//::       col: 26
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 34
//::       col: 9
//::     end:
//::       line: 34
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD1|correctness|24,18-24,18|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 24
//::       col: 18
//::     end:
//::       line: 24
//::       col: 18
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: snapshot_test_complex_5.dfy|GCD1|correctness|24,18-24,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 24
//::       col: 18
//::     end:
//::       line: 24
//::       col: 18
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD1
//::     methodType: correctness
//::     assertionGroup: GCD1
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|well-formedness|46,17-46,17|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 46
//::       col: 17
//::     end:
//::       line: 46
//::       col: 17
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: well-formedness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|well-formedness|44,14-44,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 44
//::       col: 14
//::     end:
//::       line: 44
//::       col: 18
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: well-formedness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|well-formedness|44,23-44,28|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 44
//::       col: 23
//::     end:
//::       line: 44
//::       col: 28
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: well-formedness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|well-formedness|46,19-46,19|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 46
//::       col: 19
//::     end:
//::       line: 46
//::       col: 19
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: well-formedness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|well-formedness|46,13-46,25|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 46
//::       col: 13
//::     end:
//::       line: 46
//::       col: 25
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: well-formedness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 48
//::       col: 8
//::     end:
//::       line: 48
//::       col: 8
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 44
//::       col: 14
//::     end:
//::       line: 44
//::       col: 18
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 44
//::       col: 23
//::     end:
//::       line: 44
//::       col: 28
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 46
//::       col: 13
//::     end:
//::       line: 46
//::       col: 25
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 48
//::       col: 5
//::     end:
//::       line: 48
//::       col: 10
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 49
//::       col: 8
//::     end:
//::       line: 49
//::       col: 8
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 49
//::       col: 10
//::     end:
//::       line: 49
//::       col: 10
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 49
//::       col: 5
//::     end:
//::       line: 49
//::       col: 12
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 51
//::       col: 45
//::     end:
//::       line: 51
//::       col: 45
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 51
//::       col: 47
//::     end:
//::       line: 51
//::       col: 47
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 43
//::     end:
//::       line: 53
//::       col: 47
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 63
//::     end:
//::       line: 53
//::       col: 63
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 65
//::     end:
//::       line: 53
//::       col: 65
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 75
//::     end:
//::       line: 53
//::       col: 75
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 78
//::     end:
//::       line: 53
//::       col: 82
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 78
//::     end:
//::       line: 53
//::       col: 82
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 51
//::       col: 11
//::     end:
//::       line: 51
//::       col: 54
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 11
//::     end:
//::       line: 53
//::       col: 85
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 51
//::       col: 9
//::     end:
//::       line: 53
//::       col: 87
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 55
//::       col: 43
//::     end:
//::       line: 55
//::       col: 43
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 55
//::       col: 45
//::     end:
//::       line: 55
//::       col: 45
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 54
//::       col: 5
//::     end:
//::       line: 55
//::       col: 53
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 43
//::     end:
//::       line: 57
//::       col: 43
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 45
//::     end:
//::       line: 57
//::       col: 45
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 20
//::     end:
//::       line: 57
//::       col: 24
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 29
//::     end:
//::       line: 57
//::       col: 34
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 39
//::     end:
//::       line: 57
//::       col: 51
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 9
//::     end:
//::       line: 57
//::       col: 51
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 41
//::     end:
//::       line: 59
//::       col: 45
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 61
//::     end:
//::       line: 59
//::       col: 61
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 63
//::     end:
//::       line: 59
//::       col: 63
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 73
//::     end:
//::       line: 59
//::       col: 73
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 76
//::     end:
//::       line: 59
//::       col: 80
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 76
//::     end:
//::       line: 59
//::       col: 80
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 58
//::       col: 5
//::     end:
//::       line: 59
//::       col: 84
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 40
//::     end:
//::       line: 61
//::       col: 44
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 60
//::     end:
//::       line: 61
//::       col: 60
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 62
//::     end:
//::       line: 61
//::       col: 62
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 72
//::     end:
//::       line: 61
//::       col: 72
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 75
//::     end:
//::       line: 61
//::       col: 79
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 75
//::     end:
//::       line: 61
//::       col: 79
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 56
//::     end:
//::       line: 61
//::       col: 81
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 9
//::     end:
//::       line: 61
//::       col: 81
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 63
//::       col: 12
//::     end:
//::       line: 63
//::       col: 12
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 63
//::       col: 9
//::     end:
//::       line: 63
//::       col: 14
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 65
//::       col: 17
//::     end:
//::       line: 65
//::       col: 17
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 65
//::       col: 19
//::     end:
//::       line: 65
//::       col: 19
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 64
//::       col: 9
//::     end:
//::       line: 65
//::       col: 26
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 66
//::       col: 9
//::     end:
//::       line: 66
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 68
//::       col: 17
//::     end:
//::       line: 68
//::       col: 17
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 68
//::       col: 19
//::     end:
//::       line: 68
//::       col: 19
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 68
//::       col: 25
//::     end:
//::       line: 68
//::       col: 25
//::     prooftext: >-
//::       variable 'r', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 67
//::       col: 9
//::     end:
//::       line: 68
//::       col: 26
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 70
//::       col: 12
//::     end:
//::       line: 70
//::       col: 12
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 70
//::       col: 14
//::     end:
//::       line: 70
//::       col: 14
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 70
//::       col: 9
//::     end:
//::       line: 70
//::       col: 16
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 23
//::     end:
//::       line: 73
//::       col: 27
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 43
//::     end:
//::       line: 73
//::       col: 43
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 45
//::     end:
//::       line: 73
//::       col: 45
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 55
//::     end:
//::       line: 73
//::       col: 55
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 58
//::     end:
//::       line: 73
//::       col: 62
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 58
//::     end:
//::       line: 73
//::       col: 62
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 39
//::     end:
//::       line: 73
//::       col: 64
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 13
//::     end:
//::       line: 73
//::       col: 64
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 22
//::     end:
//::       line: 76
//::       col: 26
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 9
//::     end:
//::       line: 76
//::       col: 28
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 9
//::     end:
//::       line: 76
//::       col: 28
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 78
//::       col: 17
//::     end:
//::       line: 78
//::       col: 17
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 78
//::       col: 19
//::     end:
//::       line: 78
//::       col: 19
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 78
//::       col: 25
//::     end:
//::       line: 78
//::       col: 25
//::     prooftext: >-
//::       variable 'r', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 77
//::       col: 9
//::     end:
//::       line: 78
//::       col: 26
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 81
//::       col: 13
//::     end:
//::       line: 81
//::       col: 13
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 81
//::       col: 15
//::     end:
//::       line: 81
//::       col: 15
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 81
//::       col: 21
//::     end:
//::       line: 81
//::       col: 21
//::     prooftext: >-
//::       variable 'r', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 80
//::       col: 5
//::     end:
//::       line: 81
//::       col: 22
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 82
//::       col: 1
//::     end:
//::       line: 82
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'r', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|51,18-51,18|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 51
//::       col: 18
//::     end:
//::       line: 51
//::       col: 18
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 48
//::       col: 5
//::     end:
//::       line: 48
//::       col: 10
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(6,13)-(6,26) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|6,13-6,26|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 6
//::       col: 13
//::     end:
//::       line: 6
//::       col: 26
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|53,29-53,29|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 29
//::     end:
//::       line: 53
//::       col: 29
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 49
//::       col: 5
//::     end:
//::       line: 49
//::       col: 12
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(15,23)-(15,48) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|15,23-15,48|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 15
//::       col: 23
//::     end:
//::       line: 15
//::       col: 48
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|54,5-54,5|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 54
//::       col: 5
//::     end:
//::       line: 54
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,22-57,22|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 22
//::     end:
//::       line: 57
//::       col: 22
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,31-57,31|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 31
//::     end:
//::       line: 57
//::       col: 31
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,48-57,48|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 57
//::       col: 48
//::     end:
//::       line: 57
//::       col: 48
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|58,5-58,5|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 58
//::       col: 5
//::     end:
//::       line: 58
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|61,65-61,65|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 65
//::     end:
//::       line: 61
//::       col: 65
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|73,48-73,48|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 48
//::     end:
//::       line: 73
//::       col: 48
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 70
//::       col: 9
//::     end:
//::       line: 70
//::       col: 16
//::     prooftext: ensures clause at snapshot_test_complex_5.dfy(15,23)-(15,48) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|76,24-76,24|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 24
//::     end:
//::       line: 76
//::       col: 24
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|76,18-76,18|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 18
//::     end:
//::       line: 76
//::       col: 18
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,18-76,18|Precondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 18
//::     end:
//::       line: 76
//::       col: 18
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|Call
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 76
//::       col: 9
//::     end:
//::       line: 76
//::       col: 28
//::     prooftext: requires clause at snapshot_test_complex_5.dfy(44,14)-(44,18) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|77,9-77,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 77
//::       col: 9
//::     end:
//::       line: 77
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|80,5-80,5|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 80
//::       col: 5
//::     end:
//::       line: 80
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|46,22-46,22|Postcondition
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 46
//::       col: 22
//::     end:
//::       line: 46
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|73,60-73,60|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 60
//::     end:
//::       line: 73
//::       col: 60
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|73,25-73,25|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 73
//::       col: 25
//::     end:
//::       line: 73
//::       col: 25
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|64,9-64,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 64
//::       col: 9
//::     end:
//::       line: 64
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: snapshot_test_complex_5.dfy|GCD2|correctness|67,9-67,9|AssertionManual
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 67
//::       col: 9
//::     end:
//::       line: 67
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|61,77-61,77|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 77
//::     end:
//::       line: 61
//::       col: 77
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|61,42-61,42|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 61
//::       col: 42
//::     end:
//::       line: 61
//::       col: 42
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|59,78-59,78|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 78
//::     end:
//::       line: 59
//::       col: 78
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|59,43-59,43|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 59
//::       col: 43
//::     end:
//::       line: 59
//::       col: 43
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|53,80-53,80|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 80
//::     end:
//::       line: 53
//::       col: 80
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//::   - id: >-
//::       snapshot_test_complex_5.dfy|GCD2|correctness|53,45-53,45|AssertionAutomatic
//::     file: snapshot_test_complex_5.dfy
//::     start:
//::       line: 53
//::       col: 45
//::     end:
//::       line: 53
//::       col: 45
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: GCD2
//::     methodType: correctness
//::     assertionGroup: GCD2
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_complex_5.dfy|r1|well-formedness|6,20-6,20|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|r1|well-formedness|6,20-6,20|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|r1|well-formedness|6,13-6,26|Postcondition
//::     - id: >-
//::         snapshot_test_complex_5.dfy|r4|well-formedness|15,45-15,45|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|r4|well-formedness|15,13-15,17|Postcondition
//::         - snapshot_test_complex_5.dfy|r4|well-formedness|15,43-15,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|r4|well-formedness|15,43-15,47|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_5.dfy|r4|well-formedness|15,43-15,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|r4|well-formedness|15,23-15,48|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|r4|well-formedness|15,13-15,48|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|r4|well-formedness|15,13-15,17|Postcondition
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|well-formedness|19,17-19,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|well-formedness|18,14-18,18|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|well-formedness|19,17-19,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|well-formedness|18,23-18,27|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|well-formedness|19,19-19,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|well-formedness|19,13-19,25|Postcondition
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|correctness|25,18-25,18|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|correctness|37,24-37,24|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|correctness|37,18-37,18|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,18-37,18|Precondition
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|Call
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|Call
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|Call
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|19,22-19,22|Postcondition
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|correctness|28,38-28,38|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|correctness|29,18-29,18|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,9|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,9|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,9|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD1|correctness|24,18-24,18|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|24,18-24,18|Precondition
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|Call
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,12-23,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|23,14-23,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|25,16-25,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,12-26,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|26,14-26,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|27,9-27,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,20-28,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,23-28,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,33-28,33|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,36-28,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|28,9-28,42|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|29,16-29,20|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|29,9-29,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,20-30,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,23-30,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,33-30,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,36-30,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|30,9-30,38|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|31,12-31,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,20-32,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,23-32,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|32,9-32,30|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|33,9-33,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,20-34,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,22-34,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,28-34,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|34,9-34,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|36,14-36,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,22-37,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,20-38,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,22-38,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,28-38,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|38,9-38,29|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,16-40,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,18-40,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,24-40,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|40,5-40,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD1|correctness|41,1-41,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|well-formedness|46,17-46,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|well-formedness|44,14-44,18|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|well-formedness|46,17-46,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|well-formedness|44,23-44,28|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|well-formedness|46,19-46,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|well-formedness|46,13-46,25|Postcondition
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|51,18-51,18|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|53,29-53,29|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|54,5-54,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,22-57,22|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,31-57,31|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|57,48-57,48|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|58,5-58,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|61,65-61,65|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|73,48-73,48|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|76,24-76,24|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|76,18-76,18|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,18-76,18|Precondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|Call
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|77,9-77,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|Call
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|Call
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|80,5-80,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|46,22-46,22|Postcondition
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|73,60-73,60|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|73,25-73,25|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|64,9-64,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|67,9-67,9|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|61,77-61,77|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|61,42-61,42|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|59,78-59,78|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|59,43-59,43|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|53,80-53,80|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::     - id: >-
//::         snapshot_test_complex_5.dfy|GCD2|correctness|53,45-53,45|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,43-53,47|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|48,8-48,8|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,8-49,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|49,10-49,10|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,45-51,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,47-51,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,63-53,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,65-53,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,75-53,75|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,78-53,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|51,11-51,54|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|53,11-53,85|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|51,9-53,87|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,43-55,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|55,45-55,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|54,5-55,53|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,43-57,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,45-57,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,20-57,24|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,29-57,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|57,39-57,51|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|57,9-57,51|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,41-59,45|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,61-59,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,63-59,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,73-59,73|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|59,76-59,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|58,5-59,84|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,40-61,44|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,60-61,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,62-61,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,72-61,72|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,75-61,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|61,56-61,81|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|61,9-61,81|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|63,12-63,12|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|63,9-63,14|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,17-65,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|65,19-65,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|64,9-65,26|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|66,9-66,15|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,17-68,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,19-68,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|68,25-68,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|67,9-68,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,12-70,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|70,14-70,14|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,23-73,27|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,43-73,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,45-73,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,55-73,55|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,58-73,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|73,39-73,64|AssertionManual
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|73,13-73,64|CodeLine
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,22-76,26|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|AssertionAutomatic
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|CodeLine
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,17-78,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,19-78,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|78,25-78,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|77,9-78,26|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,13-81,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,15-81,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|81,21-81,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|80,5-81,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_5.dfy|GCD2|correctness|82,1-82,1|AssertionAutomatic
//::   calls:
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|37,9-37,28|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|36,9-36,16|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|15,23-15,48|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|23,9-23,16|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|12,13-12,34|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|24,9-24,24|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|19,13-19,25|Postcondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,14-18,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|18,23-18,27|Precondition
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|26,9-26,16|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|15,23-15,48|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD1|correctness|31,9-31,14|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD1|correctness|6,13-6,26|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|48,5-48,10|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|6,13-6,26|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|49,5-49,12|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|15,23-15,48|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|70,9-70,16|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|15,23-15,48|Postcondition
//::     - id: snapshot_test_complex_5.dfy|GCD2|correctness|76,9-76,28|Call
//::       connections:
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,14-44,18|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|44,23-44,28|Precondition
//::         - snapshot_test_complex_5.dfy|GCD2|correctness|46,13-46,25|Postcondition
//::
