datatype List<T> = Nil | Cons(T, List<T>)

function reverse(xs: List): List 
decreases xs
{
    match xs
    case Nil => Nil
    case Cons(x, xrest) => append(reverse(xrest), Cons(x, Nil))
}

function append(xs: List, ys: List) : List 
decreases xs
{
    match xs
    case Nil => ys
    case Cons(x, xrest) => Cons(x, append(xrest, ys))
}

ghost method LemmaReverseTwice(xs: List) 
decreases xs;
ensures reverse(reverse(xs)) == xs
{
    match xs
    case Nil =>
    case Cons(x, xrest) =>
    // Applying the definition of reverse
    assert reverse(reverse(xs)) == reverse(append(reverse(xrest), Cons(x, Nil)));  
    // Applying the relation between append and reverse
    LemmaReverseDistAppend(reverse(xrest), Cons(x,Nil)); 
    assert reverse(append(reverse(xrest), Cons(x,Nil))) == append(reverse(Cons(x,Nil)), reverse(reverse(xrest)));
    // Applying induction hypothesis
    LemmaReverseTwice(xrest);
    assert append(reverse(Cons(x,Nil)), reverse(reverse(xrest))) == append(reverse(Cons(x, Nil)), xrest);
    // By definition of reverse
    assert append(reverse(Cons(x,Nil)), xrest) == append(Cons(x,Nil), xrest);
    // By definition of append
    assert append(Cons(x,Nil), xrest) == Cons(x, xrest);
    assert Cons(x, xrest) == xs;
}

ghost method LemmaReverseDistAppend(xs: List, ys: List)
ensures reverse(append(xs, ys)) == append(reverse(ys), reverse(xs));