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
    if( x == max(x,y)) {
        calc <= {
            power(2, x) + power(2, y);
            {LemmaMonotinictyPowerEquals(y, x);}
            power(2, x) + power(2, x);
            2 * power(2, x);
            power(2, 1 + x);
        }
    } else {
        calc <= {
            power(2, x) + power(2, y);
            {LemmaMonotinictyPowerEquals(x, y);}
            power(2, y) + power(2, y);
            2 * power(2, y);
            power(2, 1 + y);
        }

    }
}

ghost method LemmaLeavesAndHeight(tree:BinaryTree<int>) 
decreases tree
requires 0 < height(tree) 
ensures numberOfLeaves(tree) <= power(2 ,height(tree) - 1) 
{
    match tree
    case ConsBT (x, leftSubTree, rightSubTree) =>
        assert height(leftSubTree) < height(tree);
        assert height(rightSubTree) < height(tree);
        if(leftSubTree ==  Nil) {
            if(rightSubTree == Nil) {
                calc <= {
                    numberOfLeaves(tree);
                    power(2, height(tree) - 1);
                }
            } else {
                assert height(rightSubTree)-1 < height(tree)-1;
                calc <= {
                    numberOfLeaves(tree);
                    numberOfLeaves(rightSubTree);
                    { LemmaLeavesAndHeight(rightSubTree); }
                    power(2, height(rightSubTree) - 1);
                    { LemmaMonotinictyPower(height(rightSubTree)-1, height(tree)-1); }
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
                    { //LemmaMonotinictyPower(height(leftSubTree)-1, height(tree)-1); 
                    //LemmaMonotinictyPower(height(rightSubTree)-1, height(tree)-1);
                    LemmaPowers(height(leftSubTree) - 1, height(rightSubTree) - 1);
                    }
                    power(2, 1 + max(height(leftSubTree) - 1,height(rightSubTree) - 1));
                    {  assert height(tree) - 1 == 1 + max(height(leftSubTree) - 1, height(rightSubTree) - 1);}
                    // power(2, x) + power(2, y) <= power(2, 1 + max(x,y))
                     power(2, height(tree) - 1);
                }
            }
        }
}
