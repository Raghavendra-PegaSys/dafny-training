datatype Process = 0 | 1;
datatype CState =  a1 | a2 | a3a | a3b | cs | a4;
datatype State = State(pc: Process -> CState, flag: Process -> bool, turn: Process)

var pc : Process -> CState;
var flag : Process -> bool;
var turn;

function Other(p: process) : Process
{
    if p == 0 then 1 else 0
}

predicate Init(s: State) {
    s.flag(0) == s.flag(1) == false &&
    s.turn == 0 &&
    s.pc(0) == s.pc(1) == a1
}

predicate a1(p: Process, s: State, s': State) 
requires s.pc(p) == a1
{
    s'.flag(p) == true &&
    s'.pc(p) == a2
}

predicate a2(p: Process, s: State, s': State) 
requires s.pc(p) == a2
{
    s'.turn == Other(p) &&
    s'.pc(p) == a3a;
}

method a3a(p: Process, s: State, s': State) 
requires s.pc(p) == a3a
{
    (s.flag(Other(p)) && s'.pc(p) == a3b) ||
    (!s.flag(Other(p)) && s'.pc(p) == cs)
}

method a3b(p: Process, s: State, s': State) 
requires s.pc(p) == a3b)
{
    (turn == Other(p) && s'.pc(p) == a3a) ||
    (turn != Other(p) && s'.pc(p) == cs)
}

method cs(p:Process, s: State, s': State) 
requires s.pc(p) == cs)
{
    s'.pc(p) == a4
}

method a4(p: Process, s: State, s': State) 
requires s.pc(p) == a4) 
{
    s'.flag(p) == false &&
    s'.pc(p) == a1
}