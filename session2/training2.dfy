
/**
 *  Skeleton Dafny programs for session 2 of training.
 */

//=============================================================================
//  Power of 2 exercises.
//=============================================================================

/**
 *  This is the definition of powerOf2.
 */
function method powerOf2(n: nat) : nat 
    decreases n
{
    if n == 0 then 
        1
    else 
        2 * powerOf2(n - 1)
}

/**
 *  Some lemmas about powerOf2
 *  Dafny can prove this lemma automatically, but
 *  we can also provide a proof, and in that case, it will check it.
 */
lemma sumSamePowerOf2(n: nat)
    ensures powerOf2(n) + powerOf2(n) == 2 * powerOf2(n)
{
    //  You will be guided through this proof
}

//  Prove both this lemma.
lemma monotonicPowerOf2(n: nat, m: nat)
    requires n <= m
    ensures powerOf2(n) <= powerOf2(m)
{
    
}

//  Prove this lemma
lemma addPowerOf2(n: nat, m : nat)
    ensures powerOf2(n) * powerOf2(m) == powerOf2(n + m)  
{
    //  @todo: write the proof instead of assuming it.
    // assume(powerOf2(n) * powerOf2(m) == powerOf2(n + m) );
    if(n == 0) {
        calc == {
            powerOf2(n) * powerOf2(m);
            powerOf2(0) * powerOf2(m);
            1 * powerOf2(m);
            powerOf2(m);
            powerOf2(m + 0);
            powerOf2(m + n);
        }
    } else {
        calc == {
            powerOf2(n) * powerOf2(m);
            2 * powerOf2(n-1) * powerOf2(m);
            { addPowerOf2(n-1, m); }
            2 * powerOf2(n - 1 + m); 
            powerOf2(n - 1 + m + 1);
            powerOf2(n + m);
        }
    }
}

//=============================================================================
//  Tree examples 
//=============================================================================

/**
 *  Binary, non-empty trees.
 */
datatype Tree = 
        Leaf
    |   Node(left: Tree, right: Tree)

/**
 *  Maximum of two non-negative integers.
 */
function method max(x: nat, y : nat) : nat 
{
    if x > y then 
        x
    else 
        y
}

/**
 *  Height of a tree.
 *  
 *  @param  root    The root of the tree.
 *  @returns        The height of the tree rooted at `root`.
 */
function height(root : Tree) : nat 
    ensures height(root) >= 1
    decreases root
{
    match root 
        case Leaf => 1
        case Node(lc, rc) => 1 + max(height(lc), height(rc))
}

/**
 *  The number of nodes in a tree.    .
 *
 *  @param  root    The root of the tree.
 *
 *  @return         The number of nodes (including leaves) in the tree.
 *  @note           Perform a in-order (left, node, right) traversal to
 *                  compute the result.
 */
function method nodesCount(root : Tree) : nat
    ensures nodesCount(root) >= 1
{
    match root 
        case Leaf => 1
        case Node(left, right) => nodesCount(left) + nodesCount(right) + 1
}

function method leavesCount(root : Tree) : nat
    ensures leavesCount(root) >= 1
    decreases root
{
    1
}

/**
 *  The number of nodes is less than 2^(height(root)) - 1
 */
lemma upperBoundForNodesCount(root : Tree)
    ensures nodesCount(root) <= powerOf2(height(root)) - 1
{
    //  Write the proof for this lemma.
    // assume(nodesCount(root) <= powerOf2(height(root)) - 1);
    match root
        case Leaf => 
            calc {
                nodesCount(root);
                1;
                powerOf2(1) - 1;
                powerOf2(height(root)) - 1;
            }
        case Node(l, r) =>
            calc {
                nodesCount(root);
                1 + nodesCount(l) + nodesCount(r);
                {upperBoundForNodesCount(l); upperBoundForNodesCount(r); }
                <= 1 + powerOf2(height(l)) - 1 + powerOf2(height(r)) - 1;
                
            }
}

/**
 *  The number of leaves is less than 2^(height(root) - 1) 
 */
lemma upperBoundForLeavesCount(root : Tree)
    ensures leavesCount(root) <= powerOf2(height(root) - 1) 
{
    assume(leavesCount(root) <= powerOf2(height(root) - 1)); 
}

//=============================================================================
//  Main example.
//=============================================================================

//  If you want to to run the code, compile this file with:
//  dafny /noVerify /compile:4 yourPath/training2.dfy
/**
 *  Dafny compiles the Main method if it finds one in a file.
 */
method Main() {
    //  Example with powerOf2
    //  note: you need to have powerOf2 declared as a function method
    //  to be executable.
    var r := powerOf2(1);   
    print "powerOf2(1) is: ", r, "\n";

    var n:= 0;
    while n < 20 
        decreases 20 - n
    {
        var r := powerOf2(n);
        print "powerOf2(", n, ") is: ", r, "\n";
        n := n + 1;
    } 
}