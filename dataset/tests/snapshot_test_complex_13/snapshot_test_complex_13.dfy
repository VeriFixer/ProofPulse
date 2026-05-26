function RowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
{
    RowColumnProductFrom(m1, m2, row, column, 0)
}

function RowColumnProductFrom(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    decreases m1.Length1 - k
{
    if k == m1.Length1 then
        0
    else
        m1[row,k]*m2[k,column] + RowColumnProductFrom(m1, m2, row, column, k+1)
}

method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1 != null && m2 != null
    requires m1.Length1 == m2.Length0
    ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
{
    m3 := new int[m1.Length0, m2.Length1];
    var i := 0;
    while i < m1.Length0
        invariant 0 <= i <= m1.Length0
        invariant forall i', j' | 0 <= i' < i && 0 <= j' < m2.Length1 ::
            m3[i',j'] == RowColumnProduct(m1, m2, i', j')
    {
        var j := 0;

        while j < m2.Length1
            invariant 0 <= j <= m2.Length1
            invariant forall i', j' | 0 <= i' < i && 0 <= j' < m2.Length1 ::
                m3[i',j'] == RowColumnProduct(m1, m2, i', j')
            invariant forall j' | 0 <= j' < j ::
                m3[i,j'] == RowColumnProduct(m1, m2, i, j')
        {
            var k :=0;
            m3[i, j] := 0;
            while k < m1.Length1
                invariant 0 <= k <= m1.Length1
                invariant forall i', j' | 0 <= i' < i && 0 <= j' < m2.Length1 ::
                    m3[i',j'] == RowColumnProduct(m1, m2, i', j')
                invariant forall j' | 0 <= j' < j ::
                    m3[i,j'] == RowColumnProduct(m1, m2, i, j')
                invariant RowColumnProduct(m1, m2, i, j) ==
                    m3[i,j] + RowColumnProductFrom(m1, m2, i, j, k)
            {
                m3[i,j] := m3[i,j] + m1[i,k] * m2[k,j];
                k := k+1; 

            }
            j := j+1;
        }
        i := i+1;
    }
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,45-4,45|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 45
//::     end:
//::       line: 4
//::       col: 45
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,45|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 42
//::     end:
//::       line: 4
//::       col: 45
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,14-4,20|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 14
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,28-4,34|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 28
//::     end:
//::       line: 4
//::       col: 34
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,56-4,59|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 56
//::     end:
//::       line: 4
//::       col: 59
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 42
//::     end:
//::       line: 4
//::       col: 59
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,20-5,23|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 5
//::       col: 20
//::     end:
//::       line: 5
//::       col: 23
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 5
//::       col: 14
//::     end:
//::       line: 5
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,43-5,46|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 5
//::       col: 43
//::     end:
//::       line: 5
//::       col: 46
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 5
//::       col: 34
//::     end:
//::       line: 5
//::       col: 46
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,47-7,47|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 7
//::       col: 47
//::     end:
//::       line: 7
//::       col: 47
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 7
//::       col: 5
//::     end:
//::       line: 7
//::       col: 48
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,59-4,59|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 4
//::       col: 59
//::     end:
//::       line: 4
//::       col: 59
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,23-5,23|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 5
//::       col: 23
//::     end:
//::       line: 5
//::       col: 23
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,46-5,46|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 5
//::       col: 46
//::     end:
//::       line: 5
//::       col: 46
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,25-7,25|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 7
//::       col: 25
//::     end:
//::       line: 7
//::       col: 25
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProduct
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProduct
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,50-13,50|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 50
//::     end:
//::       line: 13
//::       col: 50
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 47
//::     end:
//::       line: 13
//::       col: 50
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 14
//::     end:
//::       line: 13
//::       col: 20
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 28
//::     end:
//::       line: 13
//::       col: 34
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 61
//::     end:
//::       line: 13
//::       col: 64
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 42
//::     end:
//::       line: 13
//::       col: 64
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 14
//::       col: 20
//::     end:
//::       line: 14
//::       col: 23
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 14
//::       col: 14
//::     end:
//::       line: 14
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 14
//::       col: 43
//::     end:
//::       line: 14
//::       col: 46
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 14
//::       col: 34
//::     end:
//::       line: 14
//::       col: 46
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 15
//::       col: 15
//::     end:
//::       line: 15
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 17
//::       col: 13
//::     end:
//::       line: 17
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 18
//::       col: 9
//::     end:
//::       line: 18
//::       col: 9
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 9
//::     end:
//::       line: 20
//::       col: 9
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 12
//::     end:
//::       line: 20
//::       col: 12
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 16
//::     end:
//::       line: 20
//::       col: 16
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 19
//::     end:
//::       line: 20
//::       col: 19
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 22
//::     end:
//::       line: 20
//::       col: 22
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 24
//::     end:
//::       line: 20
//::       col: 24
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 76
//::     end:
//::       line: 20
//::       col: 78
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 34
//::     end:
//::       line: 20
//::       col: 79
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 34
//::     end:
//::       line: 20
//::       col: 79
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 9
//::     end:
//::       line: 20
//::       col: 79
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 9
//::     end:
//::       line: 20
//::       col: 17
//::     prooftext: sufficient reads clause to read array element
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 19
//::     end:
//::       line: 20
//::       col: 30
//::     prooftext: sufficient reads clause to read array element
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,64-13,64|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 13
//::       col: 64
//::     end:
//::       line: 13
//::       col: 64
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,23-14,23|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 14
//::       col: 23
//::     end:
//::       line: 14
//::       col: 23
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,46-14,46|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 14
//::       col: 46
//::     end:
//::       line: 14
//::       col: 46
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,18-15,18|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 15
//::       col: 18
//::     end:
//::       line: 15
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,16-17,16|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 17
//::       col: 16
//::     end:
//::       line: 17
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 12
//::     end:
//::       line: 20
//::       col: 12
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 16
//::     end:
//::       line: 20
//::       col: 16
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 22
//::     end:
//::       line: 20
//::       col: 22
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 24
//::     end:
//::       line: 20
//::       col: 24
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,77-20,77|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 77
//::     end:
//::       line: 20
//::       col: 77
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,54-20,54|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 54
//::     end:
//::       line: 20
//::       col: 54
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,11-20,11|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 11
//::     end:
//::       line: 20
//::       col: 11
//::     prooftext: sufficient reads clause to read array element
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,21-20,21|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 20
//::       col: 21
//::     end:
//::       line: 20
//::       col: 21
//::     prooftext: sufficient reads clause to read array element
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: RowColumnProductFrom
//::     methodType: well-formedness
//::     assertionGroup: RowColumnProductFrom
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|25,17-25,17|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 25
//::       col: 17
//::     end:
//::       line: 25
//::       col: 17
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 25
//::       col: 14
//::     end:
//::       line: 25
//::       col: 17
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 24
//::       col: 14
//::     end:
//::       line: 24
//::       col: 20
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 24
//::       col: 28
//::     end:
//::       line: 24
//::       col: 34
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 25
//::       col: 28
//::     end:
//::       line: 25
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 25
//::       col: 14
//::     end:
//::       line: 25
//::       col: 31
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 13
//::     end:
//::       line: 26
//::       col: 19
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 27
//::     end:
//::       line: 26
//::       col: 30
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 41
//::     end:
//::       line: 26
//::       col: 44
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 27
//::     end:
//::       line: 26
//::       col: 44
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 55
//::     end:
//::       line: 26
//::       col: 58
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 69
//::     end:
//::       line: 26
//::       col: 72
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 55
//::     end:
//::       line: 26
//::       col: 72
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 36
//::     end:
//::       line: 27
//::       col: 39
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 27
//::     end:
//::       line: 27
//::       col: 39
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 59
//::     end:
//::       line: 27
//::       col: 62
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 50
//::     end:
//::       line: 27
//::       col: 62
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 9
//::     end:
//::       line: 28
//::       col: 9
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 12
//::     end:
//::       line: 28
//::       col: 12
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 15
//::     end:
//::       line: 28
//::       col: 15
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 46
//::     end:
//::       line: 28
//::       col: 46
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 49
//::     end:
//::       line: 28
//::       col: 49
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 21
//::     end:
//::       line: 28
//::       col: 50
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 9
//::     end:
//::       line: 28
//::       col: 50
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 13
//::     end:
//::       line: 28
//::       col: 50
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|25,31-25,31|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 25
//::       col: 31
//::     end:
//::       line: 25
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,30-26,30|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 30
//::     end:
//::       line: 26
//::       col: 30
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,44-26,44|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 44
//::     end:
//::       line: 26
//::       col: 44
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,58-26,58|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 58
//::     end:
//::       line: 26
//::       col: 58
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|26,72-26,72|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 72
//::     end:
//::       line: 26
//::       col: 72
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 12
//::     end:
//::       line: 28
//::       col: 12
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 15
//::     end:
//::       line: 28
//::       col: 15
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|28,37-28,37|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 28
//::       col: 37
//::     end:
//::       line: 28
//::       col: 37
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,62-27,62|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 62
//::     end:
//::       line: 27
//::       col: 62
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|well-formedness|27,39-27,39|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 39
//::     end:
//::       line: 27
//::       col: 39
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: well-formedness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|30,22-30,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 22
//::     end:
//::       line: 30
//::       col: 22
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 19
//::     end:
//::       line: 30
//::       col: 22
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 24
//::       col: 14
//::     end:
//::       line: 24
//::       col: 20
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 24
//::       col: 28
//::     end:
//::       line: 24
//::       col: 34
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 25
//::       col: 14
//::     end:
//::       line: 25
//::       col: 31
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 13
//::     end:
//::       line: 26
//::       col: 19
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 27
//::     end:
//::       line: 26
//::       col: 44
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 55
//::     end:
//::       line: 26
//::       col: 72
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 13
//::     end:
//::       line: 28
//::       col: 50
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 19
//::     end:
//::       line: 30
//::       col: 22
//::     prooftext: array size (dimension 0) is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 31
//::     end:
//::       line: 30
//::       col: 34
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 31
//::     end:
//::       line: 30
//::       col: 34
//::     prooftext: array size (dimension 1) is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 5
//::     end:
//::       line: 30
//::       col: 42
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 31
//::       col: 9
//::     end:
//::       line: 31
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 29
//::     end:
//::       line: 33
//::       col: 32
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 19
//::     end:
//::       line: 33
//::       col: 32
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 19
//::     end:
//::       line: 33
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 24
//::     end:
//::       line: 33
//::       col: 32
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 34
//::       col: 60
//::     end:
//::       line: 34
//::       col: 63
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 13
//::     end:
//::       line: 35
//::       col: 13
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 16
//::     end:
//::       line: 35
//::       col: 16
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 19
//::     end:
//::       line: 35
//::       col: 19
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 51
//::     end:
//::       line: 35
//::       col: 51
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 55
//::     end:
//::       line: 35
//::       col: 55
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 26
//::     end:
//::       line: 35
//::       col: 57
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 34
//::       col: 19
//::     end:
//::       line: 35
//::       col: 57
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 32
//::       col: 15
//::     end:
//::       line: 32
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 37
//::       col: 13
//::     end:
//::       line: 37
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 33
//::     end:
//::       line: 40
//::       col: 36
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 23
//::     end:
//::       line: 40
//::       col: 36
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 23
//::     end:
//::       line: 40
//::       col: 28
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 28
//::     end:
//::       line: 40
//::       col: 36
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 41
//::       col: 64
//::     end:
//::       line: 41
//::       col: 67
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 17
//::     end:
//::       line: 42
//::       col: 17
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 20
//::     end:
//::       line: 42
//::       col: 20
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 23
//::     end:
//::       line: 42
//::       col: 23
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 55
//::     end:
//::       line: 42
//::       col: 55
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 59
//::     end:
//::       line: 42
//::       col: 59
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 30
//::     end:
//::       line: 42
//::       col: 61
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 41
//::       col: 23
//::     end:
//::       line: 42
//::       col: 61
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 17
//::     end:
//::       line: 44
//::       col: 17
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 20
//::     end:
//::       line: 44
//::       col: 20
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 22
//::     end:
//::       line: 44
//::       col: 22
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 54
//::     end:
//::       line: 44
//::       col: 54
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 57
//::     end:
//::       line: 44
//::       col: 57
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 29
//::     end:
//::       line: 44
//::       col: 59
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 43
//::       col: 23
//::     end:
//::       line: 44
//::       col: 59
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 39
//::       col: 19
//::     end:
//::       line: 39
//::       col: 22
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 46
//::       col: 17
//::     end:
//::       line: 46
//::       col: 22
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 13
//::     end:
//::       line: 47
//::       col: 13
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 16
//::     end:
//::       line: 47
//::       col: 16
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 19
//::     end:
//::       line: 47
//::       col: 19
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 13
//::     end:
//::       line: 47
//::       col: 20
//::     prooftext: an array element is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 13
//::     end:
//::       line: 47
//::       col: 26
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 37
//::     end:
//::       line: 49
//::       col: 40
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 27
//::     end:
//::       line: 49
//::       col: 40
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 27
//::     end:
//::       line: 49
//::       col: 32
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 32
//::     end:
//::       line: 49
//::       col: 40
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 50
//::       col: 68
//::     end:
//::       line: 50
//::       col: 71
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 21
//::     end:
//::       line: 51
//::       col: 21
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 24
//::     end:
//::       line: 51
//::       col: 24
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 27
//::     end:
//::       line: 51
//::       col: 27
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 59
//::     end:
//::       line: 51
//::       col: 59
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 63
//::     end:
//::       line: 51
//::       col: 63
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 34
//::     end:
//::       line: 51
//::       col: 65
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 50
//::       col: 27
//::     end:
//::       line: 51
//::       col: 65
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 21
//::     end:
//::       line: 53
//::       col: 21
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 24
//::     end:
//::       line: 53
//::       col: 24
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 26
//::     end:
//::       line: 53
//::       col: 26
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 58
//::     end:
//::       line: 53
//::       col: 58
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 61
//::     end:
//::       line: 53
//::       col: 61
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 33
//::     end:
//::       line: 53
//::       col: 63
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 52
//::       col: 27
//::     end:
//::       line: 53
//::       col: 63
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 54
//::       col: 52
//::     end:
//::       line: 54
//::       col: 52
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 54
//::       col: 55
//::     end:
//::       line: 54
//::       col: 55
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 54
//::       col: 27
//::     end:
//::       line: 54
//::       col: 56
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 21
//::     end:
//::       line: 55
//::       col: 21
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 24
//::     end:
//::       line: 55
//::       col: 24
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 26
//::     end:
//::       line: 55
//::       col: 26
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 60
//::     end:
//::       line: 55
//::       col: 60
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 63
//::     end:
//::       line: 55
//::       col: 63
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 66
//::     end:
//::       line: 55
//::       col: 66
//::     prooftext: value always satisfies the subset constraints of 'nat'
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 31
//::     end:
//::       line: 55
//::       col: 67
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 54
//::       col: 27
//::     end:
//::       line: 55
//::       col: 67
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 48
//::       col: 23
//::     end:
//::       line: 48
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 17
//::     end:
//::       line: 57
//::       col: 17
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 20
//::     end:
//::       line: 57
//::       col: 20
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 22
//::     end:
//::       line: 57
//::       col: 22
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 17
//::     end:
//::       line: 57
//::       col: 23
//::     prooftext: an array element is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 28
//::     end:
//::       line: 57
//::       col: 28
//::     prooftext: >-
//::       variable 'm3', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 31
//::     end:
//::       line: 57
//::       col: 31
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 33
//::     end:
//::       line: 57
//::       col: 33
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 38
//::     end:
//::       line: 57
//::       col: 38
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 41
//::     end:
//::       line: 57
//::       col: 41
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 43
//::     end:
//::       line: 57
//::       col: 43
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 48
//::     end:
//::       line: 57
//::       col: 48
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 51
//::     end:
//::       line: 57
//::       col: 51
//::     prooftext: index 0 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 53
//::     end:
//::       line: 57
//::       col: 53
//::     prooftext: index 1 in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 17
//::     end:
//::       line: 57
//::       col: 55
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 58
//::       col: 17
//::     end:
//::       line: 58
//::       col: 25
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 48
//::       col: 13
//::     end:
//::       line: 60
//::       col: 13
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 61
//::       col: 13
//::     end:
//::       line: 61
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 39
//::       col: 9
//::     end:
//::       line: 62
//::       col: 9
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 63
//::       col: 9
//::     end:
//::       line: 63
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 32
//::       col: 5
//::     end:
//::       line: 64
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 65
//::       col: 1
//::     end:
//::       line: 65
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'm3', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|30,34-30,34|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 30
//::       col: 34
//::     end:
//::       line: 30
//::       col: 34
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,21-33,21|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 21
//::     end:
//::       line: 33
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,26-33,26|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 26
//::     end:
//::       line: 33
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|34,19-34,19|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 34
//::       col: 19
//::     end:
//::       line: 34
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|32,18-32,18|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 32
//::       col: 18
//::     end:
//::       line: 32
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,25-40,25|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 25
//::     end:
//::       line: 40
//::       col: 25
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,30-40,30|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 30
//::     end:
//::       line: 40
//::       col: 30
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|41,23-41,23|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 41
//::       col: 23
//::     end:
//::       line: 41
//::       col: 23
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|43,23-43,23|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 43
//::       col: 23
//::     end:
//::       line: 43
//::       col: 23
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|39,22-39,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 39
//::       col: 22
//::     end:
//::       line: 39
//::       col: 22
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 16
//::     end:
//::       line: 47
//::       col: 16
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 19
//::     end:
//::       line: 47
//::       col: 19
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|47,15-47,15|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 47
//::       col: 15
//::     end:
//::       line: 47
//::       col: 15
//::     prooftext: an array element is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,29-49,29|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 29
//::     end:
//::       line: 49
//::       col: 29
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,34-49,34|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 34
//::     end:
//::       line: 49
//::       col: 34
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|50,27-50,27|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 50
//::       col: 27
//::     end:
//::       line: 50
//::       col: 27
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|52,27-52,27|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 52
//::       col: 27
//::     end:
//::       line: 52
//::       col: 27
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|54,58-54,58|LoopInvariant
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 54
//::       col: 58
//::     end:
//::       line: 54
//::       col: 58
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|1,1-8,1|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 1
//::       col: 1
//::     end:
//::       line: 8
//::       col: 1
//::     prooftext: function definition for RowColumnProduct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|48,26-48,26|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 48
//::       col: 26
//::     end:
//::       line: 48
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 20
//::     end:
//::       line: 57
//::       col: 20
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 22
//::     end:
//::       line: 57
//::       col: 22
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,19-57,19|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 19
//::     end:
//::       line: 57
//::       col: 19
//::     prooftext: an array element is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 31
//::     end:
//::       line: 57
//::       col: 31
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 33
//::     end:
//::       line: 57
//::       col: 33
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 41
//::     end:
//::       line: 57
//::       col: 41
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 43
//::     end:
//::       line: 57
//::       col: 43
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 51
//::     end:
//::       line: 57
//::       col: 51
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 57
//::       col: 53
//::     end:
//::       line: 57
//::       col: 53
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|48,13-48,13|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 48
//::       col: 13
//::     end:
//::       line: 48
//::       col: 13
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: snapshot_test_complex_13.dfy|multiply|correctness|10,1-21,1|CodeLine
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 21
//::       col: 1
//::     prooftext: function definition for RowColumnProductFrom
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|39,9-39,9|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 39
//::       col: 9
//::     end:
//::       line: 39
//::       col: 9
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|54,43-54,43|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 54
//::       col: 43
//::     end:
//::       line: 54
//::       col: 43
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 24
//::     end:
//::       line: 55
//::       col: 24
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 26
//::     end:
//::       line: 55
//::       col: 26
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|55,51-55,51|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 55
//::       col: 51
//::     end:
//::       line: 55
//::       col: 51
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 24
//::     end:
//::       line: 53
//::       col: 24
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 26
//::     end:
//::       line: 53
//::       col: 26
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|53,49-53,49|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 53
//::       col: 49
//::     end:
//::       line: 53
//::       col: 49
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 24
//::     end:
//::       line: 51
//::       col: 24
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 27
//::     end:
//::       line: 51
//::       col: 27
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|51,50-51,50|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 51
//::       col: 50
//::     end:
//::       line: 51
//::       col: 50
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|50,71-50,71|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 50
//::       col: 71
//::     end:
//::       line: 50
//::       col: 71
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|49,40-49,40|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 49
//::       col: 40
//::     end:
//::       line: 49
//::       col: 40
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|32,5-32,5|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 32
//::       col: 5
//::     end:
//::       line: 32
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 20
//::     end:
//::       line: 44
//::       col: 20
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 22
//::     end:
//::       line: 44
//::       col: 22
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|44,45-44,45|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 44
//::       col: 45
//::     end:
//::       line: 44
//::       col: 45
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 20
//::     end:
//::       line: 42
//::       col: 20
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 23
//::     end:
//::       line: 42
//::       col: 23
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|42,46-42,46|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 42
//::       col: 46
//::     end:
//::       line: 42
//::       col: 46
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|41,67-41,67|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 41
//::       col: 67
//::     end:
//::       line: 41
//::       col: 67
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|40,36-40,36|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 40
//::       col: 36
//::     end:
//::       line: 40
//::       col: 36
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|26,16-26,16|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 16
//::     end:
//::       line: 26
//::       col: 16
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|26,38-26,38|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 38
//::     end:
//::       line: 26
//::       col: 38
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|26,66-26,66|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 26
//::       col: 66
//::     end:
//::       line: 26
//::       col: 66
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|27,13-27,13|Postcondition
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 27
//::       col: 13
//::     end:
//::       line: 27
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 16
//::     end:
//::       line: 35
//::       col: 16
//::     prooftext: index 0 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 19
//::     end:
//::       line: 35
//::       col: 19
//::     prooftext: index 1 in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|35,42-35,42|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 35
//::       col: 42
//::     end:
//::       line: 35
//::       col: 42
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|34,63-34,63|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 34
//::       col: 63
//::     end:
//::       line: 34
//::       col: 63
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//::   - id: >-
//::       snapshot_test_complex_13.dfy|multiply|correctness|33,32-33,32|AssertionAutomatic
//::     file: snapshot_test_complex_13.dfy
//::     start:
//::       line: 33
//::       col: 32
//::     end:
//::       line: 33
//::       col: 32
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: multiply
//::     methodType: correctness
//::     assertionGroup: multiply
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,45-4,45|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,45|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,14-4,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,28-4,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,56-4,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,20-5,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,43-5,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,47-7,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,59-4,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,56-4,59|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,14-4,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,28-4,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,20-5,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,43-5,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,47-7,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,23-5,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,20-5,23|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,14-4,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,28-4,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,56-4,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,43-5,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,47-7,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,46-5,46|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,43-5,46|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,14-4,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,28-4,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,56-4,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,20-5,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,47-7,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,25-7,25|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,14-4,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,28-4,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,56-4,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|4,42-4,59|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,20-5,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,14-5,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,43-5,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|5,34-5,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,47-7,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProduct|well-formedness|7,5-7,48|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,50-13,50|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,64-13,64|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,23-14,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,46-14,46|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,18-15,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,16-17,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,77-20,77|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,54-20,54|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,11-20,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,21-20,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,30|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,14-13,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,28-13,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,47-13,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,61-13,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|13,42-13,64|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,20-14,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,14-14,23|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,43-14,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|14,34-14,46|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|15,15-15,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|17,13-17,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|18,9-18,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,12-20,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,16-20,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,19-20,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,22-20,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,24-20,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,76-20,78|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,34-20,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,79|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|RowColumnProductFrom|well-formedness|20,9-20,17|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|25,17-25,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|25,31-25,31|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|26,30-26,30|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|26,44-26,44|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|26,58-26,58|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|26,72-26,72|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|28,37-28,37|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|27,62-27,62|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|well-formedness|27,39-27,39|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,36-27,39|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,28-25,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,30|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,41-26,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,69-26,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,27-27,39|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,59-27,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,50-27,62|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,12-28,12|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,15-28,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,46-28,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,49-28,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,21-28,50|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|28,9-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|well-formedness|27,13-28,50|Postcondition
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|30,22-30,22|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|30,34-30,34|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|33,21-33,21|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|33,26-33,26|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|34,19-34,19|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|32,18-32,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|40,25-40,25|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|40,30-40,30|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|41,23-41,23|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|43,23-43,23|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|10,1-21,1|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|39,22-39,22|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|47,15-47,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|49,29-49,29|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|49,34-49,34|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|50,27-50,27|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|52,27-52,27|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|54,58-54,58|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|1,1-8,1|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|10,1-21,1|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|48,26-48,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,19-57,19|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|48,13-48,13|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|39,9-39,9|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|54,43-54,43|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|55,51-55,51|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|53,49-53,49|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|51,50-51,50|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|50,71-50,71|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|49,40-49,40|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|32,5-32,5|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|44,45-44,45|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|42,46-42,46|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|41,67-41,67|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|40,36-40,36|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|26,16-26,16|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|26,38-26,38|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|26,66-26,66|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|27,13-27,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|35,42-35,42|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|34,63-34,63|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_13.dfy|multiply|correctness|33,32-33,32|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,29-33,32|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,14-24,20|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|24,28-24,34|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|25,14-25,31|Precondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,13-26,19|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,27-26,44|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|26,55-26,72|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|27,13-28,50|Postcondition
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,19-30,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,31-30,34|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|30,5-30,42|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|31,9-31,15|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|33,24-33,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,60-34,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,13-35,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,16-35,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,19-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,51-35,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|35,55-35,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|35,26-35,57|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|34,19-35,57|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|32,15-32,18|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|37,13-37,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,33-40,36|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,23-40,28|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|40,28-40,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,64-41,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,17-42,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,20-42,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,23-42,23|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,55-42,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|42,59-42,59|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|42,30-42,61|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|41,23-42,61|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,17-44,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,20-44,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,22-44,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,54-44,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|44,57-44,57|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|44,29-44,59|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|43,23-44,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|39,19-39,22|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|46,17-46,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,13|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,16-47,16|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,19-47,19|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,20|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|47,13-47,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,37-49,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,27-49,32|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|49,32-49,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,68-50,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,21-51,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,24-51,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,27-51,27|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,59-51,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|51,63-51,63|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|51,34-51,65|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|50,27-51,65|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,21-53,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,24-53,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,26-53,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,58-53,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|53,61-53,61|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|53,33-53,63|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|52,27-53,63|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,52-54,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,55-54,55|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|54,27-54,56|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,21-55,21|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,24-55,24|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,26-55,26|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,60-55,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,63-55,63|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|55,66-55,66|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|55,31-55,67|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|54,27-55,67|LoopInvariant
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|48,23-48,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,17|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,20-57,20|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,22-57,22|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,28-57,28|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,31-57,31|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,33-57,33|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,38-57,38|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,41-57,41|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,43-57,43|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|57,48-57,48|AssertionAutomatic
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,51-57,51|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,53-57,53|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|57,17-57,55|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|58,17-58,25|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|48,13-60,13|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|61,13-61,21|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|39,9-62,9|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|63,9-63,17|CodeLine
//::         - snapshot_test_complex_13.dfy|multiply|correctness|32,5-64,5|CodeLine
//::         - >-
//::           snapshot_test_complex_13.dfy|multiply|correctness|65,1-65,1|AssertionAutomatic
//::   calls: []
//::
