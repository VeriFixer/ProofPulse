method containsDuplicateIa(nums: seq<int>) returns (containsDuplicate: bool)
    ensures containsDuplicate <==>  exists i,j :: 0 <= i < j < |nums| && nums[i] == nums[j]
{
    var windowSet: set<int> := {};
    for i:= 0 to |nums|
        invariant forall x :: x in windowSet ==> x in nums[0..i]
        invariant forall x :: x in nums[0..i] ==> x in windowSet
        invariant !exists k,j :: 0 <= k < j < i && nums[k] == nums[j]
    {
        if nums[i] in windowSet {
            return true;
        }
        windowSet := windowSet + {nums[i]};
    }
    assert nums[0..|nums|] == nums;
    return false;
}
