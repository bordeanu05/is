method Sum(n: nat) returns (s: nat)
    ensures s == n * (n + 1) / 2
{
    var sum: nat := 0;
    var i: nat := 1;

    while i <= n
        invariant 0 <= i <= n + 1
        invariant sum == (i - 1) * i / 2
    {
        sum := sum + i;
        i := i + 1;
    }

    s := sum;
}
