// TASK: In some array arr, the values were in arithmetic progression: arr[i + 1] - arr[i] is the same for every i.
// A value from arr was removed that was not the first or last value. Given arr, return the removed value.
// Example: arr = [5,7,11,13] -> 9.  Constraints: 3 <= arr.length <= 1000; 0 <= arr[i] <= 10^5.
// SOURCE: dataset/data/veribench_Easy/task_id_1228_weak.dfy (LeetCode 1228), DafnyCert: weak
// NOTE: the method has NO ensures clause.

method MissingNumber(arr: array<int>) returns (missing: int)
    requires arr.Length >= 3
    requires arr.Length <= 1000
    requires forall i :: 0 <= i < arr.Length ==> 0 <= arr[i] <= 100000
{
    var expectedSum := (arr[0] + arr[arr.Length - 1]) * (arr.Length + 1) / 2;
    var actualSum := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant actualSum == sum(arr, i)
        invariant actualSum >= 0
    {
        actualSum := actualSum + arr[i];
        i := i + 1;
    }
    missing := expectedSum - actualSum;
    assert missing == expectedSum - actualSum;
    assert expectedSum >= 0;
    assert actualSum >= 0;
}
function sum(arr: array<int>, n: int): int
    requires 0 <= n <= arr.Length
    reads arr
{
    if n == 0 then 0
    else sum(arr, n - 1) + arr[n - 1]
}
lemma SumProperty(arr: array<int>, n: int)
    requires 0 <= n < arr.Length
    ensures sum(arr, n + 1) == sum(arr, n) + arr[n]
{
}