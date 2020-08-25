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
    && (s.turn == 0 || s.turn == 1)
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

// Get the number where the process p takes the next step in trace t
lemma LemmaGetNextScheduledStep(p: Process, t: Trace, sch: Schedule, n: nat) returns (n': nat)
requires Valid(t(n))
requires ValidProcess(p) 
requires IsTrace(t, sch)
requires FairSchedule(sch)
// p is being scheduled for the first time on or after n at n'
ensures n <= n' && sch(n') == p
ensures forall k :: n <= k <= n' ==> distanceToCS(p, t(k)) == distanceToCS(p, t(n))
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

function distanceToCS(p: Process, s: State) : nat 
requires Valid(s)
requires ValidProcess(p)
{
    match s.pc[p]
    case a1 => 4
    case a2 => 3
    case a3a => 2
    case a3b => 1
    case cs => 0
    case a4 => 5
}

predicate ProcessIsBlockedInState(p: Process, s: State)
{
    s.turn == Other(p) && s.flag[Other(p)]
}

lemma LemmaLiveness(sch: Schedule, t: Trace, p: Process, n: nat) returns (n':nat)
requires ValidProcess(p)
requires FairSchedule(sch)
requires IsTrace(t, sch)
requires t(n).flag[p]
ensures n <= n' && t(n').pc[p] == cs
{
    // Go to the position where p is waiting to enter CS
    n' := LemmaGetNextScheduledStep(p, t, sch, n);
    if(t(n').pc[p] == cs) {
        return;
    } 

    while(t(n').pc[p] != a3a && t(n').pc[p] != a3b) 
    decreases distanceToCS(p, t(n'))
    invariant NextP(p, t(n'), t(n'+1))
    invariant Valid(t(n'))
    invariant t(n').pc[p] != cs
    {
        n' := LemmaGetNextScheduledStep(p, t, sch, n'+1);
    }

    // Proceed to Critical Section case-wise
    if(t(n').pc[p] == a3a) {
        if(ProcessIsBlockedInState(p, t(n'))) {
            n' := LemmaHelper1(t, n', p, sch);
            assert !t(n').flag[Other(p)];
            n' := LemmaGetNextScheduledStep(p, t, sch, n');
            assert !t(n').flag[Other(p)]; // I have no idea how this is maintained.
            n' := n' + 1;
            assert t(n').pc[p] == cs;
        } else {
            if(t(n').flag[Other(p)]) {
                assert t(n').turn == p;
                assert t(n'+1).pc[p] == a3b;
                n' := LemmaGetNextScheduledStep(p, t, sch, n'+1);
            }             
            n' := n' + 1;
            assert t(n').pc[p] == cs;
            return;
        }
    } else {
        assert t(n').pc[p] == a3b;
        n' := LemmaHelper2(t, n, p, sch);
        assert t(n').turn == p;
        n' := LemmaGetNextScheduledStep(p, t, sch, n');
        assert t(n').turn == p; // I have no idea how this is maintained.
        n' := n' + 1;
        assert t(n').pc[p] == cs;
    }
}

lemma LemmaFlagAndPC1(s: State, p: Process)
requires Valid(s)
requires ValidProcess(p)
ensures s.pc[p] == a1 <==> !s.flag[p] 
{

}

lemma LemmaFlagAndPC2(s: State, p: Process)
requires Valid(s)
requires ValidProcess(p)
ensures (s.pc[p] == a2 || s.pc[p] == a3a || s.pc[p] == a3b || s.pc[p] == cs || s.pc[p] == a4) <==> s.flag[p] 
{

}

predicate ProcessBlockedIn(p: Process, s: State) {
    s.turn == Other(p) && s.flag[Other(p)]
}

lemma LemmaHelper1(t: Trace, n: nat, p: Process, sch: Schedule) returns (n':nat)
requires Valid(t(n))
requires ValidProcess(p)
requires IsTrace(t, sch)
requires FairSchedule(sch)
requires t(n).pc[p] == a3a
requires ProcessBlockedIn(p, t(n))
ensures n <= n' && !t(n').flag[Other(p)]
{

}

lemma LemmaHelper2(t: Trace, n: nat, p: Process, sch: Schedule) returns (n':nat)
requires Valid(t(n))
requires ValidProcess(p)
requires IsTrace(t, sch)
requires FairSchedule(sch)
requires t(n).pc[p] == a3b
ensures n <= n' && t(n').turn == p
{

}
