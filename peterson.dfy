type Process = nat
datatype CState =  a1 | a2 | a3a | a3b | cs | a4
datatype State = State(pc: map<Process, CState>, flag: map<Process, bool>, turn: Process)

predicate ValidProcess(p: Process) {
    p == 0 || p == 1
}

function Other(p: Process) : (q: Process)
requires ValidProcess(p)
ensures ValidProcess(q)
{
    if p == 0 then 1 else 0
}

predicate Valid(s: State) {
    && (forall p :: p in s.flag.Keys && ValidProcess(p))
    && (forall p :: p in s.pc.Keys && ValidProcess(p))
    && (forall p :: ValidProcess(p) && (s.pc[p] == cs ==> (s.flag[p] && s.turn == p))) 
}

predicate Init(s: State) {
    && Valid(s)
    && s.flag[0] == s.flag[1] == false
    && s.turn == 0
    && s.pc[0] == a1 && s.pc[1] == a1
}

predicate Next(s: State, s': State) {
    && Valid(s)
    && exists p : Process :: ValidProcess(p) && NextP(p, s, s')
}

predicate NextP(p: Process, s: State, s': State)
requires Valid(s) && ValidProcess(p)
{
    || (s.pc[p] == a1 && stmt_a1(p, s, s'))
    || (s.pc[p] == a2 && stmt_a2(p, s, s'))
    || (s.pc[p] == a3a && stmt_a3a(p, s, s'))
    || (s.pc[p] == a3b && stmt_a3b(p, s, s'))
    || (s.pc[p] == cs && stmt_cs(p, s, s'))
    || (s.pc[p] == a4 && stmt_a4(p, s, s'))
}

predicate stmt_a1(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s)
{
    && s.pc[p] == a1
    && s'.flag == s.flag[p := true]
    && s'.pc == s.pc[p := a2]
    && s'.turn == s.turn
}

predicate stmt_a2(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s)
{
    && s.pc[p] == a2
    && s'.turn == Other(p) 
    && s'.pc == s.pc[p := a3a]
    && s'.flag == s.flag
}

predicate stmt_a3a(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s)
{
    && s.pc[p] == a3a
    && (s.flag[Other(p)] && s'.pc == s.pc[p := a3b]) 
    && (!s.flag[Other(p)] && s'.pc == s.pc[p := cs])
    && s'.turn == s.turn
    && s'.flag == s.flag
}

predicate stmt_a3b(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) 
{
    && s.pc[p] == a3b
    && (s.turn == Other(p) && s'.pc == s.pc[p := a3a])
    && (s.turn != Other(p) && s'.pc == s.pc[p := cs])
    && s'.turn == s.turn
    && s'.flag == s.flag
}

predicate stmt_cs(p:Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) 
{
    && s.pc[p] == cs
    && s'.pc == s.pc[p := a4]
    && s'.turn == s.turn
    && s'.flag == s.flag
}

predicate stmt_a4(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) 
{
    && s.pc[p] == a4 
    && s'.flag == s.flag[p := false]
    && s'.pc == s.pc[p := a1]
    && s'.turn == s.turn
}

// Mutual Exclusion
lemma MutualExclusion(s: State, p: Process, q: Process)
requires Valid(s) && ValidProcess(p) && ValidProcess(q)
requires s.pc[p] == cs && s.pc[q] == cs
ensures p == q
{

}

// Invariance
lemma Invariance(s: State, s':State)
ensures Init(s) ==> Valid(s)
ensures Valid(s) && Next(s,s') ==> Valid(s')
{

}

// Liveness
type Schedule = nat -> Process

predicate IsSchedule(sch: Schedule) {
    forall i :: ValidProcess(sch(i))
}

predicate FairSchedule(sch: Schedule) {
    && IsSchedule(sch)
    && forall p, n :: ValidProcess(p) ==> HasNext(sch, p, n)
}

predicate HasNext(sch: Schedule, p : Process, n: nat) {
    exists n' :: n <= n' && sch(n') == p
}

type Trace = nat -> State

predicate IsTrace(t: Trace, sch: Schedule) 
requires IsSchedule(sch)
{
    && Init(t(0))
    && forall i : nat :: Valid(t(i)) && NextP(sch(i), t(i), t(i+1))
}

predicate IsProcessInCS(s: State)
requires Valid(s) 
{
    s.pc[0] == cs || s.pc[1] == cs
}

function GetProcessInCS(s: State) : Process
requires Valid(s)
requires IsProcessInCS(s)
{
    var p :| s.pc[p] == cs;
    p
}

// Get the number where the process p takes the next step in trace t
lemma LemmaGetNextScheduledStep(p: Process, t: Trace, sch: Schedule, n: nat) returns (n': nat)
requires Valid(t(n))
requires ValidProcess(p) 
requires IsTrace(t, sch)
requires FairSchedule(sch)
// p is being scheduled for the first time on or after n at n'
ensures n <= n' && sch(n') == p
// so the state of p does not change from n to n'
ensures forall i :: n <= i < n' ==> (t(i).pc[p] == t(n).pc[p] && t(i).flag[p] == t(n).flag[p])
{
    assert HasNext(sch, p, n);
    var u :| n <= u && sch(u) == p;
    n' := n;

    while sch(n') != p && n' < u
    decreases u - n'
    invariant n' <= u
    invariant forall i :: n <= i <= n' ==> (t(i).pc[p] == t(n).pc[p] && t(i).flag[p] == t(n).flag[p])
    {
        n' := n' + 1;
        assert t(n').pc[p] == t(n).pc[p] && t(n').flag[p] == t(n).flag[p];
    }
}

lemma LemmaTurnProcessGetsCSEventually(sch: Schedule, t: Trace, p: Process, n: nat) returns (n':nat)
requires ValidProcess(p)
requires t(n).flag[p] == true;
requires t(n).turn == p
requires t(n).pc[p] == a3a
ensures n <= n' && t(n').pc[p] == cs
{

}

lemma LemmaProcessRelinquishes(sch: Schedule, t: Trace, p: Process, n: nat) returns (n': nat)
requires ValidProcess(p)
requires Valid(t(n))
requires t(n).pc[p] == cs
ensures n <= n' && t(n').flag[p] == false
{

}

lemma LemmaProcessGetsCSEventually2(sch: Schedule, t: Trace, p: Process, n: nat) returns (n':nat)
requires ValidProcess(p)
requires Valid(t(n))
requires t(n).flag[Other(p)] == false
requires t(n).pc[p] == a3a
ensures n <= n' && t(n').pc[p] == cs
{

}

lemma LemmaLiveness(sch: Schedule, t: Trace, p: Process, n: nat) returns (n':nat)
requires ValidProcess(p)
requires FairSchedule(sch)
requires IsTrace(t, sch)
requires t(n).flag[p]
ensures n <= n' && t(n').pc[p] == cs
{
    n' := LemmaGetNextScheduledStep(p, t, sch, n);
    assert NextP(p, t(n'), t(n'+1));

    match t(n').pc[p]
    case a4 =>
    {
        // Push it to n' where t(n').pc[p] == a1
        assume t(n').pc[p] == cs;
    }

    case a1 => 
        // Push it to the place when t(n').pc[p] == a3a
        assert t(n'+1).pc[p] == a2;
        assume t(n').pc[p] == cs;
        n' := LemmaLiveness(sch, t, p, n'+1); // Problem with proving termination
        assert t(n').pc[p] == cs;

    case a2 =>
        assert t(n'+1).pc[p] == a3a;
        assume t(n').pc[p] == cs;
        n' := LemmaLiveness(sch, t, p, n'+1); // Problem with proving termination
        assert t(n').pc[p] == cs;

    case a3a =>
    if t(n').flag[Other(p)] == true
    {
        // Get the next step n' where t(n').pc[p] == a3b
        assert t(n'+1).pc[p] == a3b;
        n' := LemmaLiveness(sch, t, p, n'+1);
        assert t(n').pc[p] == cs;
    } else {
        n' := LemmaGetNextScheduledStep(p, t, sch, n'+1);
        assert t(n').pc[p] == cs;
    }

    case a3b =>
        assert t(n').turn == p || t(n').turn == Other(p);
        if t(n').turn == p
        {
            // Jump to n' where t(n').pc[p] == cs
            n' := n' + 1;
            assert t(n').pc[p] == cs;
        } else {
            n' := n' + 1;
            assert t(n'+1).pc[p] == a3a;
            if t(n').flag[Other(p)] == true
            {
                // 1. Jump to the state 
                // We can prove that we reach n' s.t. pc[Other(p)] == cs using the above lemma
                // And then it will relinquish saying that we reach n'' s.t. flag[Other(p)] == false
                // From then it is same as 2b
            } else

                // t(n').turn == Other(p) && t(n').flag[Other(p)] == false
            {
                // Reach n' such that pc[p] == a3a
                assume t(n').pc[p] == cs;
            }
        }
    
    case cs =>
        return;
}