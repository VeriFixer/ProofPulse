method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{
	var i: nat := 1;
	max := a[0];
	while i < a.Length
	invariant 0 <= i <= a.Length
	invariant forall j :: 0 <= j < i ==> a[j] <= max //:: Not used lurking
	invariant exists j :: 0 <= j < i && a[j] == max //:: Not used lurking
	{
		if (a[i] > max) {
			max := a[i];
		}
		i := i + 1;
	}
}

method Main() {
	var arr : array<int> := new int[][-11,2,42,-4];
	var res := MaxArray(arr);
	assert arr[0] == -11 && arr[1] == 2 && arr[2] == 42 && arr[3] == -4;
	assert res == 42;
}

//::: Testing methods bugs an overview
// Results for Main (correctness)
//   Overall outcome: Correct
//   Overall time: 00:00:00.0912142
//   Overall resource count: 28954
//   Maximum assertion batch time: 00:00:00.0912142
//   Maximum assertion batch resource count: 28954

//   Assertion batch 1:
//     Outcome: Valid
//     Duration: 00:00:00.0912142
//     Resource count: 28954

//     Assertions:
//       max_array.dfy(21,33): array size is never negative
//       max_array.dfy(21,33): given array size agrees with the number of expressions in the initializing display (4)
//       max_array.dfy(22,13): the precondition always holds
//       max_array.dfy(23,9): array is never null
//       max_array.dfy(23,12): index in range
//       max_array.dfy(23,9): assertion always holds
//       max_array.dfy(23,26): assertion always holds
//       max_array.dfy(23,41): assertion always holds
//       max_array.dfy(23,57): assertion always holds
//       max_array.dfy(24,13): assertion always holds
//       max_array.dfy(23,57): array is never null
//       max_array.dfy(23,60): index in range
//       max_array.dfy(23,41): array is never null
//       max_array.dfy(23,44): index in range
//       max_array.dfy(23,26): array is never null
//       max_array.dfy(23,29): index in range

//     Proof dependencies:
//       max_array.dfy(21,33)-(21,33): array size is never negative
//       max_array.dfy(21,33)-(21,33): given array size agrees with the number of expressions in the initializing display (4)
//       max_array.dfy(22,10)-(22,26): ensures clause at max_array.dfy(3,9)-(3,51) from call
//       max_array.dfy(22,10)-(22,26): ensures clause at max_array.dfy(4,9)-(4,50) from call
//       max_array.dfy(22,10)-(22,26): requires clause at max_array.dfy(2,10)-(2,21) from call
//       max_array.dfy(23,9)-(23,9): array is never null
//       max_array.dfy(23,9)-(23,20): assertion always holds
//       max_array.dfy(23,9)-(23,14): index in range
//       max_array.dfy(23,26)-(23,26): array is never null
//       max_array.dfy(23,26)-(23,36): assertion always holds
//       max_array.dfy(23,26)-(23,31): index in range
//       max_array.dfy(23,41)-(23,41): array is never null
//       max_array.dfy(23,41)-(23,51): assertion always holds
//       max_array.dfy(23,41)-(23,46): index in range
//       max_array.dfy(23,57)-(23,57): array is never null
//       max_array.dfy(23,57)-(23,68): assertion always holds
//       max_array.dfy(23,57)-(23,62): index in range
//       max_array.dfy(24,2)-(24,18): assertion always holds

//     Unused by proof:
//       max_array.dfy(21,23)-(21,48): assignment (or return)
//       max_array.dfy(22,10)-(22,26): call
//       max_array.dfy(22,10)-(22,26): assignment (or return)
//       max_array.dfy(23,9)-(23,68): assert statement
// :::


//::: Conclusions
// For complex assertions that are individualized the coverage is not catching that
// if every assertions was used to prove it, that the global is also used
// namely all this are proven and appear as dependecnies
//       max_array.dfy(23,9): array is never null
//       max_array.dfy(23,12): index in range
//       max_array.dfy(23,9): assertion always holds
//       max_array.dfy(23,26): assertion always holds
//       max_array.dfy(23,41): assertion always holds
//       max_array.dfy(23,57): assertion always holds
//       max_array.dfy(24,13): assertion always holds
//       max_array.dfy(23,57): array is never null
//       max_array.dfy(23,60): index in range
//       max_array.dfy(23,41): array is never null
//       max_array.dfy(23,44): index in range
//       max_array.dfy(23,26): array is never null
//       max_array.dfy(23,29): index in range