method CopyInt(a: nat) returns (b: nat)
    // Uncomment to try the example
    // requires a >= 0 // (technically redundant as a: nat)
    ensures b == a
{
    var i: nat := a;
    b := 0;
    while i > 0
        // Technically these were not needed
        invariant i <= a
        invariant b >= 0
        invariant i >= 0
        // The right invariant!
        invariant a == b + i
        // This also works
        // invariant a - i == b
    {
        i := i - 1;
        b := b + 1;
    }
    // What do I know here?
}

// Another one for the following poll
method AddOne(a: nat) returns (b: nat)
    // Uncomment to try the example
    ensures b == a + 1
{
    b := 0;
    while b < a + 1
        invariant b <= a + 1
    {
        b := b + 1;
    }
}


method Find(a: seq<int>, key: int) returns (index: int)
    ensures 0 <= index < |a| ==> a[index] == key
    ensures index == |a| ==> forall k :: 0 <= k < |a| ==> a[k] != key
{
    index := 0;
    while (index < |a|) && (a[index] != key)
        invariant index <= |a|
        invariant forall k :: 0 <= k < index ==> a[k] != key
    {
        index := index + 1;
    }
    // We know that index == |a| OR a[index] == key
    // We know that forall k :: 0 <= k < |a| ==> a[k] != key
}
