// Exercise 0
method max(x: int, y: int) returns (z: int)
ensures z == x || z == y;
ensures z >= x && z >= y;
{
    if(x >= y) {
        return x;
    } else {
        return y;
    }
}

// Exercise 1
method testMax() {
    var k := max(5, 8);
    assert k == 8; 
}

// Exercise 2
method Abs(x: int) returns (y: int)
requires x < 0;
ensures 0 <= y;
ensures 0 <= x ==> y == x;
ensures x < 0 ==> y == -x;
{
        y := -x;
}

// Exercise 3
method Abs2(x: int) returns (y: int)
requires x == -1;
ensures 0 <= y;
ensures 0 <= x ==> y == x;
ensures x < 0 ==> y == -x;
{
        y := x + 2;
}

method Abs3(x: int) returns (y: int)
//ensures 0 <= y;
//ensures 0 <= x ==> y == x;
//ensures x < 0 ==> y == -x;
{
        y := x + 1;
}

// Replacing y = x + 1 in the post conditions, we have that 
// 0 <= x ==> x + 1 == x. FALSEHOOD
// x < 0 ==> x + 1 == -x ==> x == 1/2, which is not an integer
// Hence there is no solution, or no precondition can satisfy
// for y := x + 1

// Excercise 4
function maxfn(x: int, y: int) : int
{
    if (x >= y) then x else y
}

method testMaxfn() {
    assert 34 < maxfn (35, 77);
    assert maxfn(34, 45) > maxfn(34,12);
}

// Excercise 5
function method maxfnMet(x: int, y: int) : int
{
    if (x >= y) then x else y
}

method testMaxfnMet() {
    var k := maxfnMet (35, 77);
    assert 34 < k;
}

// Exercise 6 , easy

// Exercise 7
method loop1(n: nat) {
    var i := 0;
    while (i < n)
    invariant 0 <= i <= n+2;
    {
        i := i + 1;
    }
    // The loop invariant still verifies, but the below assert does not hold 
    // assert i == n;
}

// Exercise 8
method loop2(n: nat) {
    var i := 0;
    while (i != n)
    invariant 0 <= i <= n;
    {
        i := i + 1;
    }
    assert i == n;
    // Yes, it does.
}

// Exercise 9
function fib(n : nat) : nat {
    if (n == 0) then 0 else 
    if (n == 1) then 1 else
        fib(n-1) + fib(n-2)
}

method ComputeFib(n: nat) returns (b: nat)
ensures b == fib(n);
{
    if (n == 0) { return 0; }
    var i := 1;
    b := 1;
    var c := 1;
    while ( i < n) 
        invariant 0 < i <= n;
        invariant c == fib(i+1);
        invariant b == fib(i);
    {
        b, c := c, b + c;
        i := i + 1;
    }
}

// Exercise 10
method ComputeFib2(n: nat) returns (b: nat)
ensures b == fib(n);
{
    var i := 0;
    b := 0;
    var a := 1;
    while ( i < n) 
        invariant 0 <= i <= n;
        invariant a == fib(i+1);
        invariant b == fib(i);
    {
        b, a := a, b + a;
        i := i + 1;
    }
}

// Exercise 11
// Does not verify because Dafny cannot deduce that i is bounded by n, hence n - i is not lower 
// bounded. See by commenting the loop invariant.
method termination(n: nat) {
    var i := 0;
    while(i != n)
        invariant i <= n;
        decreases n - i;
    {
        i := i + 1;
    }
}

// Exercise 12
method maxInArray(a: array<int>) returns (maxIndex:nat)
requires a.Length >= 1;
ensures 0 <= maxIndex < a.Length;
ensures forall k:: 0 <= k < a.Length ==>  a[maxIndex] >= a[k];
ensures a[maxIndex] in a[..];

{
    var i := 1;
    var max := a[0];
    maxIndex := 0;
    while (i < a.Length)
    invariant 1 <= i <= a.Length;
    invariant 0 <= maxIndex < i;
    invariant a[maxIndex] == max;
    invariant forall k :: 0 <= k < i ==> a[maxIndex] >= a[k];
    invariant a[maxIndex] in a[..i];
    decreases a.Length - i;
    {
        if(a[i] > max) {
            max := a[i];
            maxIndex := i;
        }
        i := i + 1;
    }

}

// Exercise 12b
method maxInArray2(a: array<int>) returns (max:int)
requires a.Length >= 1
ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
ensures max in a[..]
{
    var i := 1;
    max := a[0];
    while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> max >= a[k]
    invariant max in a[..i]
    decreases a.Length - i;
    {
        if(a[i] > max) {
            max := a[i];
        }
        i := i + 1;
    }
}

// Exercise 13 done in training.

// Exercise 14
function sorted(a: array<int>) : bool 
reads a
{
    if (a.Length == 0) then 
        false 
    else 
        forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Exercise 15
method BinarySearch(a: array<int>, key: int) returns (index:int) 
requires sorted(a)
ensures 0 <= index ==> index < a.Length && a[index] == key
ensures 0 > index ==> (forall k :: (0 <= k < a.Length) ==> a[k] != key)
{
    var low, high := 0, a.Length;

    while (low < high)
    decreases high - low; 
    invariant 0 <= low <= high <= a.Length;
    invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != key
    {
        var mid := (low + high) / 2;
        if(key < a[mid]) {
            high := mid;
        } else if (key > a[mid]) {
            low := mid + 1;
        } else {
            index := mid;
            return;
        }
    }
    return -1;
}

// Setting low to mid breaks termination, as high - low may not always decrease
// Setting high to mid - 1 breaks both the loop invariants