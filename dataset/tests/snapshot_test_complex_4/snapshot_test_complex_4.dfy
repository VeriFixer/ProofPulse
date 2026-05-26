// ASSIGNMENT P1
// CMSC 433 FALL 2023
// PERFECT SCORE:  100 POINTS
//
// This assignment contains nine questions, each of which involves writing Dafny
// code. You should include your solutions in a single Dafny file and submit it using
// Gradescope.
//
// Revision history
//
// 2023-09-22 2:50 pm   Fixed typo in Problem 3.


// Question 1 (5 points)
//
// Fill in a requires clause that enables Dafny to verify
// method PlusOne

method PlusOne (x : int) returns (y : int)
    requires x >= 0
    ensures y > 0
{
    y := x+1;
}


// Question 2 (5 points)
//
// Fill in requires clause(s) that enable(s) Dafny to verify the array bounds
// in method Swap (which swaps elements i and j in array a).

method Swap (a : array?<int>, i : int, j : int)
    requires a != null && 0 <= i < a.Length && 0 <= j < a.Length// TODO
    modifies a  // Dafny requires listing of objects modified in a method
{
    var tmp : int := a[i];
    a[i] := a[j];
    a[j] := a[i];
}

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures m == n * d + r && 0 <= r < n // TODO
{
    return m / n, m % n;
}

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length && 
        forall i : int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i] // TODO
{
    c := new int [a.Length];  // Creates new array of size a.Length
    var i : int := 0;
    while (i < a.Length)
        invariant i <= a.Length
        invariant forall j : int :: 0 <= j < i ==> c[j] == a[j] + b[j]
    {
        c[i] := a[i] + b[i];
        i := i + 1;
    }
}

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator).  Write requires and
// ensures clauses for the method header Euclid below.  Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

method Euclid (m : int, n : int) returns (gcd : int)
    requires m > 1 && n > 1 && m >= n  // TODO
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0 // TODO
    

    // YOU DO NOT NEED TO IMPLEMENT Euclid!!

// Question 6 (10 points)
//
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// returns true if and only if array a is sorted.

method IsSorted (a : array<int>) returns (isSorted : bool)
    ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{
    isSorted := true;
    var i : int := 1;
    if (a.Length < 2)
    {
        return;
    }
    else
    {
        while (i < a.Length)
            invariant  1 <= i <= a.Length
            invariant isSorted <==> forall j: int :: 1 <= j < i ==> a[j-1] <= a[j] // TODO
        {
            if a[i-1] > a[i]
            {
                return false;
            }
            i := i+1;
        }
    }
}

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

method IsPrime (m : int) returns (isPrime : bool)
    requires m > 0 // m must be greater than 0
    ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0) 
	// ensures states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
{
    isPrime := true; // asume is prime initially
    
    if m <= 1 {
        isPrime := false;
    } else {
        var i : int := 2;
        
        while (i < m)
            invariant isPrime <==> forall j : int :: 2 <= j < i ==> m % j != 0
            // invariant specifies that isPrime is true iff at each j from 2 to i-1, not j | m
        {
            if (m % i == 0)
            {
                isPrime := false;
                break;
            }
            i := i + 1;
        }
    }
    
}

// Question 8 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.

method Reverse (a : array<int>) returns (aRev : array<int>)
    ensures aRev.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
    ensures fresh(aRev) // Indicates returned object is newly created in method body
{
    aRev := new int[a.Length];
    var i : int := 0;
    while (i < a.Length)
        invariant 0 <= i <= a.Length
        invariant forall j : int :: 0 <= j < i ==> aRev[j] == a[a.Length-j-1]
    {
        aRev[i] := a[a.Length-i-1];
        i := i + 1;
    }
}

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

method NoDups (a : array<int>) returns (noDups : bool)
    requires forall j : int :: 0 < j < a.Length ==> a[j-1] <= a[j] // a sorted
    ensures noDups <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] != a[j]
{
    noDups := true;
    var i : int := 1;

    if (a.Length < 2)
    {
        return;
    }

    while (i < a.Length)
        invariant 1 <= i <= a.Length
        invariant noDups <==> forall j : int :: 1 <= j < i ==> a[j-1] != a[j]
    {
        if (a[i-1] == a[i])
        {
            noDups := false;
            break;
        }
        i := i + 1;
    }
}



//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: snapshot_test_complex_4.dfy|PlusOne|correctness|21,15-21,15|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 21
//::       col: 15
//::     end:
//::       line: 21
//::       col: 15
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: PlusOne
//::     methodType: correctness
//::     assertionGroup: PlusOne
//::   - id: snapshot_test_complex_4.dfy|PlusOne|correctness|20,14-20,19|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 20
//::       col: 14
//::     end:
//::       line: 20
//::       col: 19
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: PlusOne
//::     methodType: correctness
//::     assertionGroup: PlusOne
//::   - id: snapshot_test_complex_4.dfy|PlusOne|correctness|21,13-21,17|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 21
//::       col: 13
//::     end:
//::       line: 21
//::       col: 17
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: PlusOne
//::     methodType: correctness
//::     assertionGroup: PlusOne
//::   - id: snapshot_test_complex_4.dfy|PlusOne|correctness|23,5-23,13|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 13
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: PlusOne
//::     methodType: correctness
//::     assertionGroup: PlusOne
//::   - id: >-
//::       snapshot_test_complex_4.dfy|PlusOne|correctness|24,1-24,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 24
//::       col: 1
//::     end:
//::       line: 24
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'y', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: PlusOne
//::     methodType: correctness
//::     assertionGroup: PlusOne
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 36
//::       col: 22
//::     end:
//::       line: 36
//::       col: 22
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 14
//::     end:
//::       line: 33
//::       col: 19
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 27
//::     end:
//::       line: 33
//::       col: 32
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 32
//::     end:
//::       line: 33
//::       col: 38
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 48
//::     end:
//::       line: 33
//::       col: 53
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 53
//::     end:
//::       line: 33
//::       col: 59
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 36
//::       col: 22
//::     end:
//::       line: 36
//::       col: 25
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 36
//::       col: 9
//::     end:
//::       line: 36
//::       col: 26
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 5
//::     end:
//::       line: 37
//::       col: 5
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 5
//::     end:
//::       line: 37
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 13
//::     end:
//::       line: 37
//::       col: 13
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 13
//::     end:
//::       line: 37
//::       col: 16
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 5
//::     end:
//::       line: 37
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 5
//::     end:
//::       line: 38
//::       col: 5
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 5
//::     end:
//::       line: 38
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 13
//::     end:
//::       line: 38
//::       col: 13
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 13
//::     end:
//::       line: 38
//::       col: 16
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 5
//::     end:
//::       line: 38
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|36,23-36,23|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 36
//::       col: 23
//::     end:
//::       line: 36
//::       col: 23
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|37,6-37,6|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 6
//::     end:
//::       line: 37
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|37,14-37,14|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 37
//::       col: 14
//::     end:
//::       line: 37
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|correctness|38,6-38,6|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 6
//::     end:
//::       line: 38
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|correctness|38,14-38,14|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 38
//::       col: 14
//::     end:
//::       line: 38
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: correctness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|well-formedness|33,59-33,59|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 59
//::     end:
//::       line: 33
//::       col: 59
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|well-formedness|33,14-33,19|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 14
//::     end:
//::       line: 33
//::       col: 19
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|well-formedness|33,57-33,59|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 57
//::     end:
//::       line: 33
//::       col: 59
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|well-formedness|33,36-33,38|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 36
//::     end:
//::       line: 33
//::       col: 38
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|well-formedness|33,27-33,38|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 27
//::     end:
//::       line: 33
//::       col: 38
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: snapshot_test_complex_4.dfy|Swap|well-formedness|33,48-33,59|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 48
//::     end:
//::       line: 33
//::       col: 59
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Swap|well-formedness|33,38-33,38|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 33
//::       col: 38
//::     end:
//::       line: 33
//::       col: 38
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Swap
//::     methodType: well-formedness
//::     assertionGroup: Swap
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IntDiv|correctness|52,14-52,14|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 52
//::       col: 14
//::     end:
//::       line: 52
//::       col: 14
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|49,14-49,18|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 49
//::       col: 14
//::     end:
//::       line: 49
//::       col: 18
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|52,12-52,16|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 52
//::       col: 12
//::     end:
//::       line: 52
//::       col: 16
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,13-50,26|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 50
//::       col: 13
//::     end:
//::       line: 50
//::       col: 26
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,31-50,36|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 50
//::       col: 31
//::     end:
//::       line: 50
//::       col: 36
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,36-50,40|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 50
//::       col: 36
//::     end:
//::       line: 50
//::       col: 40
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 52
//::       col: 5
//::     end:
//::       line: 52
//::       col: 24
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|52,19-52,23|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 52
//::       col: 19
//::     end:
//::       line: 52
//::       col: 23
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 52
//::       col: 5
//::     end:
//::       line: 52
//::       col: 24
//::     prooftext: >-
//::       out-parameter 'd', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IntDiv|correctness|53,1-53,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 53
//::       col: 1
//::     end:
//::       line: 53
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'd', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IntDiv|correctness|52,21-52,21|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 52
//::       col: 21
//::     end:
//::       line: 52
//::       col: 21
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,15-50,15|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 50
//::       col: 15
//::     end:
//::       line: 50
//::       col: 15
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,33-50,33|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 50
//::       col: 33
//::     end:
//::       line: 50
//::       col: 33
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,38-50,38|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 50
//::       col: 38
//::     end:
//::       line: 50
//::       col: 38
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: IntDiv
//::     methodType: correctness
//::     assertionGroup: IntDiv
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,16-62,16|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 62
//::       col: 16
//::     end:
//::       line: 62
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 62
//::       col: 14
//::     end:
//::       line: 62
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 62
//::       col: 26
//::     end:
//::       line: 62
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 62
//::       col: 14
//::     end:
//::       line: 62
//::       col: 28
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 13
//::     end:
//::       line: 63
//::       col: 15
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 25
//::     end:
//::       line: 63
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 13
//::     end:
//::       line: 63
//::       col: 27
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 36
//::     end:
//::       line: 64
//::       col: 38
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 27
//::     end:
//::       line: 64
//::       col: 38
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 49
//::     end:
//::       line: 64
//::       col: 49
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 49
//::     end:
//::       line: 64
//::       col: 52
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 57
//::     end:
//::       line: 64
//::       col: 57
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 57
//::     end:
//::       line: 64
//::       col: 60
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 64
//::     end:
//::       line: 64
//::       col: 64
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 64
//::     end:
//::       line: 64
//::       col: 67
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 49
//::     end:
//::       line: 64
//::       col: 67
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 27
//::     end:
//::       line: 64
//::       col: 67
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 9
//::     end:
//::       line: 64
//::       col: 67
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,28-62,28|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 62
//::       col: 28
//::     end:
//::       line: 62
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,15-63,15|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 15
//::     end:
//::       line: 63
//::       col: 15
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,27-63,27|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 27
//::     end:
//::       line: 63
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,50-64,50|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 50
//::     end:
//::       line: 64
//::       col: 50
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,58-64,58|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 58
//::     end:
//::       line: 64
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,65-64,65|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 65
//::     end:
//::       line: 64
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,38-64,38|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 38
//::     end:
//::       line: 64
//::       col: 38
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: well-formedness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|66,21-66,21|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 66
//::       col: 21
//::     end:
//::       line: 66
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 66
//::       col: 19
//::     end:
//::       line: 66
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 62
//::       col: 14
//::     end:
//::       line: 62
//::       col: 28
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 13
//::     end:
//::       line: 63
//::       col: 27
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 9
//::     end:
//::       line: 64
//::       col: 67
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 66
//::       col: 19
//::     end:
//::       line: 66
//::       col: 21
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 66
//::       col: 5
//::     end:
//::       line: 66
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 67
//::       col: 9
//::     end:
//::       line: 67
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 69
//::       col: 24
//::     end:
//::       line: 69
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 69
//::       col: 19
//::     end:
//::       line: 69
//::       col: 26
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 52
//::     end:
//::       line: 70
//::       col: 52
//::     prooftext: >-
//::       variable 'c', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 52
//::     end:
//::       line: 70
//::       col: 55
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 60
//::     end:
//::       line: 70
//::       col: 60
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 60
//::     end:
//::       line: 70
//::       col: 63
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 67
//::     end:
//::       line: 70
//::       col: 67
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 67
//::     end:
//::       line: 70
//::       col: 70
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 19
//::     end:
//::       line: 70
//::       col: 70
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 68
//::       col: 16
//::     end:
//::       line: 68
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 9
//::     end:
//::       line: 72
//::       col: 9
//::     prooftext: >-
//::       variable 'c', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 9
//::     end:
//::       line: 72
//::       col: 12
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 17
//::     end:
//::       line: 72
//::       col: 17
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 17
//::     end:
//::       line: 72
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 24
//::     end:
//::       line: 72
//::       col: 24
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 24
//::     end:
//::       line: 72
//::       col: 27
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 9
//::     end:
//::       line: 72
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 73
//::       col: 9
//::     end:
//::       line: 73
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 68
//::       col: 5
//::     end:
//::       line: 74
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 75
//::       col: 1
//::     end:
//::       line: 75
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'c', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|69,21-69,21|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 69
//::       col: 21
//::     end:
//::       line: 69
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,19|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 19
//::     end:
//::       line: 70
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|68,18-68,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 68
//::       col: 18
//::     end:
//::       line: 68
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,10-72,10|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 10
//::     end:
//::       line: 72
//::       col: 10
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,18-72,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 18
//::     end:
//::       line: 72
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|72,25-72,25|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 72
//::       col: 25
//::     end:
//::       line: 72
//::       col: 25
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-68,5|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 68
//::       col: 5
//::     end:
//::       line: 68
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|63,22-63,22|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 63
//::       col: 22
//::     end:
//::       line: 63
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,9|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 64
//::       col: 9
//::     end:
//::       line: 64
//::       col: 9
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|69,26-69,26|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 69
//::       col: 26
//::     end:
//::       line: 69
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,53-70,53|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 53
//::     end:
//::       line: 70
//::       col: 53
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,61-70,61|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 61
//::     end:
//::       line: 70
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|ArraySum|correctness|70,68-70,68|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 70
//::       col: 68
//::     end:
//::       line: 70
//::       col: 68
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ArraySum
//::     methodType: correctness
//::     assertionGroup: ArraySum
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,50-89,50|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 50
//::     end:
//::       line: 89
//::       col: 50
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,13-89,19|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 13
//::     end:
//::       line: 89
//::       col: 19
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: snapshot_test_complex_4.dfy|Euclid|well-formedness|89,48-89,52|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 48
//::     end:
//::       line: 89
//::       col: 52
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|88,14-88,18|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 88
//::       col: 14
//::     end:
//::       line: 88
//::       col: 18
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|88,23-88,27|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 88
//::       col: 23
//::     end:
//::       line: 88
//::       col: 27
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|88,32-88,37|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 88
//::       col: 32
//::     end:
//::       line: 88
//::       col: 37
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,24-89,31|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 24
//::     end:
//::       line: 89
//::       col: 31
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,36-89,43|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 36
//::     end:
//::       line: 89
//::       col: 43
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,48-89,59|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 48
//::     end:
//::       line: 89
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: snapshot_test_complex_4.dfy|Euclid|well-formedness|89,64-89,68|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 64
//::     end:
//::       line: 89
//::       col: 68
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,64-89,75|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 64
//::     end:
//::       line: 89
//::       col: 75
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Euclid|well-formedness|89,66-89,66|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 89
//::       col: 66
//::     end:
//::       line: 89
//::       col: 66
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Euclid
//::     methodType: well-formedness
//::     assertionGroup: Euclid
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,67|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 67
//::     end:
//::       line: 100
//::       col: 67
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,54-100,56|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 54
//::     end:
//::       line: 100
//::       col: 56
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,72|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 67
//::     end:
//::       line: 100
//::       col: 72
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,77|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 77
//::     end:
//::       line: 100
//::       col: 77
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,80|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 77
//::     end:
//::       line: 100
//::       col: 80
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,13-100,80|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 13
//::     end:
//::       line: 100
//::       col: 80
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,68-100,68|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 68
//::     end:
//::       line: 100
//::       col: 68
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,78-100,78|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 78
//::     end:
//::       line: 100
//::       col: 78
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,56-100,56|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 56
//::     end:
//::       line: 100
//::       col: 56
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: well-formedness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|104,11-104,11|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 104
//::       col: 11
//::     end:
//::       line: 104
//::       col: 11
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 104
//::       col: 9
//::     end:
//::       line: 104
//::       col: 11
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 13
//::     end:
//::       line: 100
//::       col: 80
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 102
//::       col: 5
//::     end:
//::       line: 102
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 103
//::       col: 9
//::     end:
//::       line: 103
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 106
//::       col: 9
//::     end:
//::       line: 106
//::       col: 15
//::     prooftext: >-
//::       out-parameter 'isSorted', which is subject to definite-assignment rules,
//::       is always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 34
//::     end:
//::       line: 111
//::       col: 36
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 24
//::     end:
//::       line: 111
//::       col: 36
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 24
//::     end:
//::       line: 111
//::       col: 29
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 29
//::     end:
//::       line: 111
//::       col: 36
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 23
//::     end:
//::       line: 112
//::       col: 23
//::     prooftext: >-
//::       variable 'isSorted', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 69
//::     end:
//::       line: 112
//::       col: 69
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 69
//::     end:
//::       line: 112
//::       col: 74
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 79
//::     end:
//::       line: 112
//::       col: 79
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 79
//::     end:
//::       line: 112
//::       col: 82
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 23
//::     end:
//::       line: 112
//::       col: 82
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 110
//::       col: 20
//::     end:
//::       line: 110
//::       col: 22
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 114
//::       col: 16
//::     end:
//::       line: 114
//::       col: 16
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 114
//::       col: 16
//::     end:
//::       line: 114
//::       col: 21
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 114
//::       col: 25
//::     end:
//::       line: 114
//::       col: 25
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 114
//::       col: 25
//::     end:
//::       line: 114
//::       col: 28
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 116
//::       col: 17
//::     end:
//::       line: 116
//::       col: 29
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 116
//::       col: 17
//::     end:
//::       line: 116
//::       col: 29
//::     prooftext: >-
//::       out-parameter 'isSorted', which is subject to definite-assignment rules,
//::       is always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 118
//::       col: 13
//::     end:
//::       line: 118
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 110
//::       col: 9
//::     end:
//::       line: 119
//::       col: 9
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 121
//::       col: 1
//::     end:
//::       line: 121
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'isSorted', which is subject to definite-assignment rules,
//::       is always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,26-111,26|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 26
//::     end:
//::       line: 111
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,31-111,31|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 31
//::     end:
//::       line: 111
//::       col: 31
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,32-112,32|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 32
//::     end:
//::       line: 112
//::       col: 32
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|110,22-110,22|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 110
//::       col: 22
//::     end:
//::       line: 110
//::       col: 22
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|100,22-100,22|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 100
//::       col: 22
//::     end:
//::       line: 100
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|114,17-114,17|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 114
//::       col: 17
//::     end:
//::       line: 114
//::       col: 17
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|114,26-114,26|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 114
//::       col: 26
//::     end:
//::       line: 114
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-110,9|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 110
//::       col: 9
//::     end:
//::       line: 110
//::       col: 9
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|111,36-111,36|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 111
//::       col: 36
//::     end:
//::       line: 111
//::       col: 36
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,70-112,70|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 70
//::     end:
//::       line: 112
//::       col: 70
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsSorted|correctness|112,80-112,80|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 112
//::       col: 80
//::     end:
//::       line: 112
//::       col: 80
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsSorted
//::     methodType: correctness
//::     assertionGroup: IsSorted
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|well-formedness|130,71-130,71|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 130
//::       col: 71
//::     end:
//::       line: 130
//::       col: 71
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: well-formedness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|well-formedness|130,69-130,73|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 130
//::       col: 69
//::     end:
//::       line: 130
//::       col: 73
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: well-formedness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|well-formedness|129,14-129,18|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 129
//::       col: 14
//::     end:
//::       line: 129
//::       col: 18
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsPrime
//::     methodType: well-formedness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|well-formedness|130,13-130,79|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 130
//::       col: 13
//::     end:
//::       line: 130
//::       col: 79
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsPrime
//::     methodType: well-formedness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|141,31-141,31|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 141
//::       col: 31
//::     end:
//::       line: 141
//::       col: 31
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 133
//::       col: 5
//::     end:
//::       line: 133
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 138
//::       col: 13
//::     end:
//::       line: 138
//::       col: 25
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 141
//::       col: 23
//::     end:
//::       line: 141
//::       col: 78
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|129,14-129,18|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 129
//::       col: 14
//::     end:
//::       line: 129
//::       col: 18
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|130,13-130,79|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 130
//::       col: 13
//::     end:
//::       line: 130
//::       col: 79
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|136,9-136,25|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 136
//::       col: 9
//::     end:
//::       line: 136
//::       col: 25
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,23|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 141
//::       col: 23
//::     end:
//::       line: 141
//::       col: 23
//::     prooftext: >-
//::       variable 'isPrime', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|141,69-141,73|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 141
//::       col: 69
//::     end:
//::       line: 141
//::       col: 73
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|144,17-144,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 144
//::       col: 17
//::     end:
//::       line: 144
//::       col: 21
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|146,17-146,33|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 146
//::       col: 17
//::     end:
//::       line: 146
//::       col: 33
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 149
//::       col: 13
//::     end:
//::       line: 149
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|140,20-140,20|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 140
//::       col: 20
//::     end:
//::       line: 140
//::       col: 20
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-150,9|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 140
//::       col: 9
//::     end:
//::       line: 150
//::       col: 9
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|153,1-153,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 153
//::       col: 1
//::     end:
//::       line: 153
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'isPrime', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|144,19-144,19|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 144
//::       col: 19
//::     end:
//::       line: 144
//::       col: 19
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-140,9|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 140
//::       col: 9
//::     end:
//::       line: 140
//::       col: 9
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|130,21-130,21|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 130
//::       col: 21
//::     end:
//::       line: 130
//::       col: 21
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|IsPrime|correctness|141,71-141,71|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 141
//::       col: 71
//::     end:
//::       line: 141
//::       col: 71
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsPrime
//::     methodType: correctness
//::     assertionGroup: IsPrime
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|163,18-163,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 18
//::     end:
//::       line: 163
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 13
//::     end:
//::       line: 163
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 28
//::     end:
//::       line: 163
//::       col: 30
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 13
//::     end:
//::       line: 163
//::       col: 30
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 40
//::     end:
//::       line: 164
//::       col: 42
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 31
//::     end:
//::       line: 164
//::       col: 42
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 53
//::     end:
//::       line: 164
//::       col: 53
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 53
//::     end:
//::       line: 164
//::       col: 56
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 61
//::     end:
//::       line: 164
//::       col: 61
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 66
//::     end:
//::       line: 164
//::       col: 71
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 61
//::     end:
//::       line: 164
//::       col: 81
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 53
//::     end:
//::       line: 164
//::       col: 81
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 31
//::     end:
//::       line: 164
//::       col: 81
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 13
//::     end:
//::       line: 164
//::       col: 81
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 165
//::       col: 13
//::     end:
//::       line: 165
//::       col: 23
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|163,30-163,30|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 30
//::     end:
//::       line: 163
//::       col: 30
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,54-164,54|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 54
//::     end:
//::       line: 164
//::       col: 54
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,71-164,71|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 71
//::     end:
//::       line: 164
//::       col: 71
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,65-164,65|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 65
//::     end:
//::       line: 164
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|well-formedness|164,42-164,42|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 42
//::     end:
//::       line: 164
//::       col: 42
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: well-formedness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|167,23-167,23|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 167
//::       col: 23
//::     end:
//::       line: 167
//::       col: 23
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 167
//::       col: 21
//::     end:
//::       line: 167
//::       col: 23
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 13
//::     end:
//::       line: 163
//::       col: 30
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 13
//::     end:
//::       line: 164
//::       col: 81
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 165
//::       col: 13
//::     end:
//::       line: 165
//::       col: 23
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 167
//::       col: 21
//::     end:
//::       line: 167
//::       col: 23
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 167
//::       col: 5
//::     end:
//::       line: 167
//::       col: 30
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 168
//::       col: 9
//::     end:
//::       line: 168
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 29
//::     end:
//::       line: 170
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 19
//::     end:
//::       line: 170
//::       col: 31
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 19
//::     end:
//::       line: 170
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 24
//::     end:
//::       line: 170
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 52
//::     end:
//::       line: 171
//::       col: 52
//::     prooftext: >-
//::       variable 'aRev', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 52
//::     end:
//::       line: 171
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 63
//::     end:
//::       line: 171
//::       col: 63
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 65
//::     end:
//::       line: 171
//::       col: 67
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 63
//::     end:
//::       line: 171
//::       col: 77
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 19
//::     end:
//::       line: 171
//::       col: 77
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 169
//::       col: 16
//::     end:
//::       line: 169
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 9
//::     end:
//::       line: 173
//::       col: 9
//::     prooftext: >-
//::       variable 'aRev', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 9
//::     end:
//::       line: 173
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 20
//::     end:
//::       line: 173
//::       col: 20
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 22
//::     end:
//::       line: 173
//::       col: 24
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 20
//::     end:
//::       line: 173
//::       col: 34
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 9
//::     end:
//::       line: 173
//::       col: 35
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 174
//::       col: 9
//::     end:
//::       line: 174
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 169
//::       col: 5
//::     end:
//::       line: 175
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 176
//::       col: 1
//::     end:
//::       line: 176
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'aRev', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,21-170,21|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 21
//::     end:
//::       line: 170
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,26-170,26|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 26
//::     end:
//::       line: 170
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,19|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 19
//::     end:
//::       line: 171
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|169,18-169,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 169
//::       col: 18
//::     end:
//::       line: 169
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,13-173,13|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 13
//::     end:
//::       line: 173
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,24-173,24|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 24
//::     end:
//::       line: 173
//::       col: 24
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|173,21-173,21|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 173
//::       col: 21
//::     end:
//::       line: 173
//::       col: 21
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|169,5-169,5|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 169
//::       col: 5
//::     end:
//::       line: 169
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|163,25-163,25|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 163
//::       col: 25
//::     end:
//::       line: 163
//::       col: 25
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,13|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 164
//::       col: 13
//::     end:
//::       line: 164
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,13|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 165
//::       col: 13
//::     end:
//::       line: 165
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,56-171,56|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 56
//::     end:
//::       line: 171
//::       col: 56
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,67-171,67|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 67
//::     end:
//::       line: 171
//::       col: 67
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|171,64-171,64|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 171
//::       col: 64
//::     end:
//::       line: 171
//::       col: 64
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|Reverse|correctness|170,31-170,31|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 170
//::       col: 31
//::     end:
//::       line: 170
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Reverse
//::     methodType: correctness
//::     assertionGroup: Reverse
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 53
//::     end:
//::       line: 186
//::       col: 53
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 40
//::     end:
//::       line: 186
//::       col: 42
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 32
//::     end:
//::       line: 186
//::       col: 42
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 53
//::     end:
//::       line: 186
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 63
//::     end:
//::       line: 186
//::       col: 63
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 63
//::     end:
//::       line: 186
//::       col: 66
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 53
//::     end:
//::       line: 186
//::       col: 66
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 32
//::     end:
//::       line: 186
//::       col: 66
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 14
//::     end:
//::       line: 186
//::       col: 66
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 52
//::     end:
//::       line: 187
//::       col: 54
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 65
//::     end:
//::       line: 187
//::       col: 65
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 65
//::     end:
//::       line: 187
//::       col: 70
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 75
//::     end:
//::       line: 187
//::       col: 75
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 75
//::     end:
//::       line: 187
//::       col: 78
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 13
//::     end:
//::       line: 187
//::       col: 78
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,54-186,54|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 54
//::     end:
//::       line: 186
//::       col: 54
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,64-186,64|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 64
//::     end:
//::       line: 186
//::       col: 64
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,66-187,66|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 66
//::     end:
//::       line: 187
//::       col: 66
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,76-187,76|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 76
//::     end:
//::       line: 187
//::       col: 76
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|187,54-187,54|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 54
//::     end:
//::       line: 187
//::       col: 54
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|well-formedness|186,42-186,42|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 42
//::     end:
//::       line: 186
//::       col: 42
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: well-formedness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|192,11-192,11|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 192
//::       col: 11
//::     end:
//::       line: 192
//::       col: 11
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 192
//::       col: 9
//::     end:
//::       line: 192
//::       col: 11
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 186
//::       col: 14
//::     end:
//::       line: 186
//::       col: 66
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 13
//::     end:
//::       line: 187
//::       col: 78
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 189
//::       col: 5
//::     end:
//::       line: 189
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 190
//::       col: 9
//::     end:
//::       line: 190
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 194
//::       col: 9
//::     end:
//::       line: 194
//::       col: 15
//::     prooftext: >-
//::       out-parameter 'noDups', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 29
//::     end:
//::       line: 198
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 19
//::     end:
//::       line: 198
//::       col: 31
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 19
//::     end:
//::       line: 198
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 24
//::     end:
//::       line: 198
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 19
//::     end:
//::       line: 199
//::       col: 19
//::     prooftext: >-
//::       variable 'noDups', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 64
//::     end:
//::       line: 199
//::       col: 64
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 64
//::     end:
//::       line: 199
//::       col: 69
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 74
//::     end:
//::       line: 199
//::       col: 74
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 74
//::     end:
//::       line: 199
//::       col: 77
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 19
//::     end:
//::       line: 199
//::       col: 77
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 197
//::       col: 16
//::     end:
//::       line: 197
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 201
//::       col: 13
//::     end:
//::       line: 201
//::       col: 13
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 201
//::       col: 13
//::     end:
//::       line: 201
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 201
//::       col: 23
//::     end:
//::       line: 201
//::       col: 23
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 201
//::       col: 23
//::     end:
//::       line: 201
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 203
//::       col: 13
//::     end:
//::       line: 203
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 206
//::       col: 9
//::     end:
//::       line: 206
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 197
//::       col: 5
//::     end:
//::       line: 207
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 208
//::       col: 1
//::     end:
//::       line: 208
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'noDups', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|198,21-198,21|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 21
//::     end:
//::       line: 198
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|198,26-198,26|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 26
//::     end:
//::       line: 198
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|199,26-199,26|LoopInvariant
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 26
//::     end:
//::       line: 199
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|197,18-197,18|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 197
//::       col: 18
//::     end:
//::       line: 197
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|201,14-201,14|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 201
//::       col: 14
//::     end:
//::       line: 201
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|201,24-201,24|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 201
//::       col: 24
//::     end:
//::       line: 201
//::       col: 24
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|197,5-197,5|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 197
//::       col: 5
//::     end:
//::       line: 197
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: snapshot_test_complex_4.dfy|NoDups|correctness|187,20-187,20|Postcondition
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 187
//::       col: 20
//::     end:
//::       line: 187
//::       col: 20
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|198,31-198,31|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 198
//::       col: 31
//::     end:
//::       line: 198
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,65-199,65|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 65
//::     end:
//::       line: 199
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//::   - id: >-
//::       snapshot_test_complex_4.dfy|NoDups|correctness|199,75-199,75|AssertionAutomatic
//::     file: snapshot_test_complex_4.dfy
//::     start:
//::       line: 199
//::       col: 75
//::     end:
//::       line: 199
//::       col: 75
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: NoDups
//::     methodType: correctness
//::     assertionGroup: NoDups
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_complex_4.dfy|PlusOne|correctness|21,15-21,15|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|PlusOne|correctness|20,14-20,19|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|PlusOne|correctness|21,13-21,17|Postcondition
//::         - snapshot_test_complex_4.dfy|PlusOne|correctness|23,5-23,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|PlusOne|correctness|24,1-24,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|correctness|36,23-36,23|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|correctness|37,6-37,6|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|correctness|37,14-37,14|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|correctness|38,6-38,6|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|correctness|38,14-38,14|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,32-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,16|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,14-33,19|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,27-33,32|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,48-33,53|Precondition
//::         - snapshot_test_complex_4.dfy|Swap|correctness|33,53-33,59|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|36,22-36,22|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|36,9-36,26|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|37,13-37,16|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|37,5-37,17|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|correctness|38,13-38,13|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Swap|correctness|38,5-38,17|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|well-formedness|33,59-33,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,14-33,19|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,57-33,59|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,36-33,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,27-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,48-33,59|Precondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Swap|well-formedness|33,38-33,38|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,14-33,19|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,36-33,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,27-33,38|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,57-33,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Swap|well-formedness|33,48-33,59|Precondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IntDiv|correctness|52,14-52,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|49,14-49,18|Precondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,12-52,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,13-50,26|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,31-50,36|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,36-50,40|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,19-52,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|53,1-53,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IntDiv|correctness|52,21-52,21|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,12-52,16|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,19-52,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|49,14-49,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,13-50,26|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,31-50,36|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,36-50,40|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|53,1-53,1|AssertionAutomatic
//::     - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,15-50,15|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,13-50,26|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,12-52,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|49,14-49,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,31-50,36|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,36-50,40|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,19-52,23|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|53,1-53,1|AssertionAutomatic
//::     - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,33-50,33|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,31-50,36|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,12-52,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|49,14-49,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,13-50,26|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,36-50,40|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,19-52,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|53,1-53,1|AssertionAutomatic
//::     - id: snapshot_test_complex_4.dfy|IntDiv|correctness|50,38-50,38|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|49,14-49,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,36-50,40|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,12-52,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,13-50,26|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|50,31-50,36|Postcondition
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|CodeLine
//::         - snapshot_test_complex_4.dfy|IntDiv|correctness|52,19-52,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|52,5-52,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IntDiv|correctness|53,1-53,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,16-62,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,28-62,28|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,15-63,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,27-63,27|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,50-64,50|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,58-64,58|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,65-64,65|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,38-64,38|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,36-64,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,26-62,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,25-63,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,38|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,57-64,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,64-64,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,49-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,27-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|well-formedness|64,9-64,67|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|66,21-66,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|69,21-69,21|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,19|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|68,18-68,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|72,10-72,10|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|72,18-72,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|72,25-72,25|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-68,5|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|63,22-63,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,9|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|69,26-69,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|70,53-70,53|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|70,61-70,61|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|ArraySum|correctness|70,68-70,68|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|62,14-62,28|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,70|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|63,13-63,27|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|64,9-64,67|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,19-66,21|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|66,5-66,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|67,9-67,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,24-69,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|69,19-69,26|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,52-70,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,60-70,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,67-70,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|70,19-70,70|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|68,16-68,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,17-72,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|72,24-72,27|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|72,9-72,28|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|73,9-73,19|CodeLine
//::         - snapshot_test_complex_4.dfy|ArraySum|correctness|68,5-74,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|ArraySum|correctness|75,1-75,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Euclid|well-formedness|89,50-89,50|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,13-89,19|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,48-89,52|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|88,14-88,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|88,23-88,27|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|88,32-88,37|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,24-89,31|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,36-89,43|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,48-89,59|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,64-89,68|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,64-89,75|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Euclid|well-formedness|89,66-89,66|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,48-89,52|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,64-89,68|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|88,14-88,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|88,23-88,27|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|88,32-88,37|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,13-89,19|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,24-89,31|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,36-89,43|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,48-89,59|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Euclid|well-formedness|89,64-89,75|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,67|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,54-100,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,13-100,80|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,68-100,68|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,72|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,54-100,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,13-100,80|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,78-100,78|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,80|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,54-100,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,13-100,80|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,56-100,56|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,54-100,56|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,67-100,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,77-100,80|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|well-formedness|100,13-100,80|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|104,11-104,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|111,26-111,26|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|111,31-111,31|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|112,32-112,32|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|110,22-110,22|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|100,22-100,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|114,17-114,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|114,26-114,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-110,9|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|111,36-111,36|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|112,70-112,70|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsSorted|correctness|112,80-112,80|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,82|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|100,13-100,80|Postcondition
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|102,5-102,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|103,9-103,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|104,9-104,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|106,9-106,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,34-111,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,24-111,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|111,29-111,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,69-112,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,79-112,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|112,23-112,82|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|110,20-110,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,16-114,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|114,25-114,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|116,17-116,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|118,13-118,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsSorted|correctness|110,9-119,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsSorted|correctness|121,1-121,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsPrime|well-formedness|130,71-130,71|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|well-formedness|130,69-130,73|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|well-formedness|129,14-129,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|well-formedness|130,13-130,79|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsPrime|correctness|141,31-141,31|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|129,14-129,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|130,13-130,79|Postcondition
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|136,9-136,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|141,69-141,73|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|144,17-144,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|146,17-146,33|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|140,20-140,20|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-150,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|153,1-153,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsPrime|correctness|144,19-144,19|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|144,17-144,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|129,14-129,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|130,13-130,79|Postcondition
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|136,9-136,25|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|141,69-141,73|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|146,17-146,33|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|140,20-140,20|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-150,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|153,1-153,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-140,9|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-150,9|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|129,14-129,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|130,13-130,79|Postcondition
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|136,9-136,25|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|141,69-141,73|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|144,17-144,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|146,17-146,33|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|140,20-140,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|153,1-153,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsPrime|correctness|130,21-130,21|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|130,13-130,79|Postcondition
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|136,9-136,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|146,17-146,33|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|129,14-129,18|Precondition
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|141,69-141,73|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|144,17-144,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|140,20-140,20|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-150,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|153,1-153,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|IsPrime|correctness|141,71-141,71|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|141,69-141,73|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|129,14-129,18|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|130,13-130,79|Postcondition
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|133,5-133,20|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|136,9-136,25|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|138,13-138,25|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|141,23-141,78|LoopInvariant
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|144,17-144,21|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|146,17-146,33|CodeLine
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|149,13-149,23|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|140,20-140,20|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|IsPrime|correctness|140,9-150,9|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|IsPrime|correctness|153,1-153,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|well-formedness|163,18-163,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|well-formedness|163,30-163,30|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|well-formedness|164,54-164,54|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|well-formedness|164,71-164,71|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|well-formedness|164,65-164,65|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|well-formedness|164,42-164,42|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,40-164,42|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,28-163,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,42|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,66-164,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,61-164,81|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,53-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,31-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|well-formedness|165,13-165,23|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|167,23-167,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|170,21-170,21|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|170,26-170,26|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,19|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|169,18-169,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|173,13-173,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|173,24-173,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|173,21-173,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|169,5-169,5|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|163,25-163,25|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|171,56-171,56|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|171,67-171,67|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|171,64-171,64|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|Reverse|correctness|170,31-170,31|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,29-170,31|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|163,13-163,30|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|164,13-164,81|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|165,13-165,23|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,21-167,23|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|167,5-167,30|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|168,9-168,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,19-170,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|170,24-170,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,52-171,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,65-171,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,63-171,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|171,19-171,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|169,16-169,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,22-173,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|173,20-173,34|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|173,9-173,35|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|174,9-174,19|CodeLine
//::         - snapshot_test_complex_4.dfy|Reverse|correctness|169,5-175,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|Reverse|correctness|176,1-176,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|186,54-186,54|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|186,64-186,64|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|187,66-187,66|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|187,76-187,76|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|187,54-187,54|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|well-formedness|186,42-186,42|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,40-186,42|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,42|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,63-186,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,53-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,32-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,52-187,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,65|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,65-187,70|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,75|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,75-187,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|well-formedness|187,13-187,78|Postcondition
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|192,11-192,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|198,21-198,21|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|198,26-198,26|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|199,26-199,26|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|197,18-197,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|201,14-201,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|201,24-201,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|197,5-197,5|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|187,20-187,20|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|198,31-198,31|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|199,65-199,65|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_4.dfy|NoDups|correctness|199,75-199,75|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,77|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|186,14-186,66|Precondition
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|187,13-187,78|Postcondition
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|189,5-189,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|190,9-190,21|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|192,9-192,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|194,9-194,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,29-198,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,19-198,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|198,24-198,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,64-199,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,74-199,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|199,19-199,77|LoopInvariant
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|197,16-197,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,13-201,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|201,23-201,26|AssertionAutomatic
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|203,13-203,28|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|206,9-206,19|CodeLine
//::         - snapshot_test_complex_4.dfy|NoDups|correctness|197,5-207,5|CodeLine
//::         - >-
//::           snapshot_test_complex_4.dfy|NoDups|correctness|208,1-208,1|AssertionAutomatic
//::   calls: []
//::
