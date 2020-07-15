datatype BinaryTree<T> = Nil | ConsBT (val: T, left: BinaryTree<T>, right: BinaryTree<T>) 

function method max(x: int, y: int) : int
ensures x <= max(x,y)
ensures y <= max(x,y)
ensures max(x,y) in {x,y}
{
    if( x < y) then y else x
}

function method height(tree : BinaryTree) : nat
decreases tree
{
    match tree
    case Nil => 0
    case ConsBT(x, leftSubTree, rightSubTree) => 
        1 + max(height(leftSubTree), height(rightSubTree))
}

function method numberOfLeaves(tree: BinaryTree) : int
decreases tree
{
    match tree
    case Nil => 0
    case ConsBT(x, leftSubTree, rightSubTree) => 
        if leftSubTree == Nil && rightSubTree == Nil then 
            1 
        else
            numberOfLeaves(leftSubTree) + numberOfLeaves(rightSubTree)
        
}

function method numberOfNodes(tree : BinaryTree) : int
decreases tree
{
    match tree
    case Nil => 0
    case ConsBT(l, leftSubTree, rightSubTree) => 1 + numberOfNodes(leftSubTree) + numberOfNodes(rightSubTree)
}

function method power(x: int, y: nat) : int
decreases y
{
    if(y == 0) then 1
    else x * power(x, y-1)
}

method Main() {
    var tree := ConsBT(2, ConsBT(3, Nil, Nil), ConsBT(4, Nil, Nil));
    print "Number of leaves = ", numberOfLeaves(tree), "\n";
    print "Number of nodes = ", numberOfNodes(tree), "\n";
    print "Height = ", height(tree), "\n";
}

ghost method LemmaMonotinictyPower(x: nat, y: nat)
requires x < y
ensures power(2, x) <= power(2, y)
{
    // Thanks Dafny
}

ghost method LemmaMonotinictyPowerEquals(x: nat, y: nat)
requires x <= y
ensures power(2, x) <= power(2, y)
{
    // Thanks Dafny
}

lemma LemmaPowers(x: nat, y: nat)
ensures power(2, x) + power(2, y) <= power(2, 1 + max(x,y))
{
    var z := max(x, y);
    calc <= {
        power(2, x) + power(2, y);
        {LemmaMonotinictyPowerEquals(x, z); LemmaMonotinictyPowerEquals(y, z);}
        power(2, z) + power(2, z);
        2 * power(2, z);
        power(2, 1 + z);
        power(2, 1 + max(x, y));
    }
}

lemma LemmaLeavesAndHeight(tree:BinaryTree<int>) 
decreases tree
requires 0 < height(tree) 
ensures numberOfLeaves(tree) <= power(2 ,height(tree) - 1) 
{
    match tree
    case ConsBT (x, leftSubTree, rightSubTree) =>
        if(leftSubTree ==  Nil) {
            if(rightSubTree == Nil) {
                calc <= {
                    numberOfLeaves(tree);
                    power(2, height(tree) - 1);
                }
            } else {
                calc <= {
                    numberOfLeaves(tree);
                    numberOfLeaves(rightSubTree);
                    { LemmaLeavesAndHeight(rightSubTree); }
                    power(2, height(rightSubTree) - 1);
                    { assert height(rightSubTree)-1 < height(tree)-1;
                    LemmaMonotinictyPower(height(rightSubTree)-1, height(tree)-1); }
                    power(2, height(tree) - 1);
                }
            }
        } else {
            assert height(leftSubTree)-1 < height(tree)-1;
            assert height(rightSubTree)-1 < height(tree)-1;
            if(rightSubTree == Nil) {
                calc <= {
                    numberOfLeaves(tree);
                    numberOfLeaves(leftSubTree);
                    { LemmaLeavesAndHeight(leftSubTree); }
                    power(2, height(leftSubTree) - 1);
                    { LemmaMonotinictyPower(height(leftSubTree)-1, height(tree)-1); }
                    power(2, height(tree) - 1);
                }
            } else {
                calc <= {
                    numberOfLeaves(tree);
                    numberOfLeaves(leftSubTree) + numberOfLeaves(rightSubTree);
                    { LemmaLeavesAndHeight(rightSubTree); LemmaLeavesAndHeight(leftSubTree); }
                    power(2, height(leftSubTree) - 1) + power(2, height(rightSubTree) - 1);
                    { LemmaPowers(height(leftSubTree) - 1, height(rightSubTree) - 1); }
                    power(2, 1 + max(height(leftSubTree) - 1,height(rightSubTree) - 1));
                    {  assert height(tree) - 1 == 1 + max(height(leftSubTree) - 1, height(rightSubTree) - 1);}
                    power(2, height(tree) - 1);
                }
            }
        }
}

lemma LemmaPowerIncrement(x: nat)
ensures power(2, x) <= power(2, x+1) - 1
{

}

lemma LemmaNodesAndHeight(tree: BinaryTree<int>)
requires 0 < height(tree)
ensures numberOfNodes(tree) <= power(2, height(tree)) - 1
{
    var level := 0;
    var numNodesInCurrentLevel := 1;
    match tree
    case ConsBT (val, left, right) =>
        if(left == Nil) {
            if(right == Nil) { 
                calc <= {
                    numberOfNodes(tree);
                    power(2, height(tree)) - 1;
                }
            } else {
                calc <= {
                    numberOfNodes(tree);
                    1 + numberOfNodes(right);
                    { LemmaNodesAndHeight(right); }
                    1 + power(2, height(right)) - 1;
                    power(2, height(right));
                    { LemmaPowerIncrement(height(right));}
                    power(2, height(right)+1) - 1;
                    { assert height(right) + 1 == height(tree); }
                    power(2, height(tree)) - 1;
                }
            }
        } else {
            if(right == Nil) {
                calc <= {
                    numberOfNodes(tree);
                    1 + numberOfNodes(left);
                    { LemmaNodesAndHeight(left); }
                    1 + power(2, height(left)) - 1;
                    power(2, height(left));
                    { LemmaPowerIncrement(height(left));}
                    power(2, height(left)+1) - 1;
                    { assert height(left) + 1 == height(tree); }
                    power(2, height(tree)) - 1;
                }
            } else {
                var maxH := max(height(left), height(right));
                calc <= {
                    numberOfNodes(tree);
                    1 + numberOfNodes(left) + numberOfNodes(right);
                    { LemmaNodesAndHeight(left); LemmaNodesAndHeight(right); }
                    1 + power(2, height(left)) - 1 + power(2, height(right)) - 1;
                    { LemmaMonotinictyPowerEquals(height(left), maxH); 
                    LemmaMonotinictyPowerEquals(height(right), maxH); } 
                    1 + power(2, maxH) - 1 + power(2, maxH) - 1;
                    power(2, maxH) + power(2, maxH) - 1;
                    power(2, maxH + 1) - 1;
                    { assert height(tree) == 1 + maxH; }
                    power(2, height(tree)) - 1;
                }
            }
        }
}

predicate completeTree(tree: BinaryTree<int>) {
    match tree
    case Nil => true
    case ConsBT(val, left, right) => 
        height(left) == height(right) && completeTree(left) && completeTree(right)
}

lemma LemmaLeavesAndHeightComplete(tree: BinaryTree<int>)
requires completeTree(tree)
requires 0 < height(tree)
ensures numberOfLeaves(tree) == power(2, height(tree) - 1)
{
    match tree
    case ConsBT(val, left, right) =>
        if(left == Nil && right == Nil) {
            calc {
                numberOfLeaves(tree);
                power(2, height(tree) - 1);
            }
        } else {
            calc {
                numberOfLeaves(tree);
                numberOfLeaves(left) + numberOfLeaves(right);
                {LemmaLeavesAndHeightComplete(left); LemmaLeavesAndHeightComplete(right); }
                power(2, height(left) - 1) + power(2, height(right) - 1);
                { assert height(left) == height(right);  }
                power(2, height(left) - 1) + power(2, height(left) - 1);
                2 * power(2, height(left) - 1);
                power(2, height(left) + 1 -1);
                { assert height(tree) == 1 + height(left); }
                power(2, height(tree) - 1);
            }
        }
}

lemma LemmaNodesAndHeightComplete(tree: BinaryTree<int>)
requires completeTree(tree)
requires 0 < height(tree)
ensures numberOfNodes(tree) == power(2, height(tree)) - 1
{
    match tree
    case ConsBT(val, left, right) =>
        if(left == Nil && right == Nil) {
            calc {
                numberOfNodes(tree);
                power(2, height(tree)) - 1;
            }
        }  else {
            calc {
                numberOfNodes(tree);
                1 + numberOfNodes(left) + numberOfNodes(right);
                {LemmaNodesAndHeightComplete(left); LemmaNodesAndHeightComplete(right); }
                1 + power(2, height(left)) - 1 + power(2, height(right)) - 1;
                { assert height(left) == height(right); }
                2 * power(2, height(left)) - 1;
                power(2, 1 + height(left)) - 1;
                { assert height(tree) == 1 + height(left); }
                power(2, height(tree)) - 1;
            }
        }
}