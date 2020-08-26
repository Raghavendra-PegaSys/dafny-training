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
    && (forall p :: ValidProcess(p) && (s.pc[p] != a1 <==> s.flag[p]))
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
ensures n <= n' 
// p is being scheduled for the first time on or after n at n'
ensures forall k :: n <= k < n' ==> sch(k) != p
ensures sch(n') == p
// the state of p does not change from n to n'
ensures forall i :: n <= i <= n' ==> (t(i).pc[p] == t(n).pc[p] && t(i).flag[p] == t(n).flag[p])
// p has not executed, hence distance does not change
ensures forall k :: n <= k <= n' ==> distanceToCS(p, t(k)) == distanceToCS(p, t(n))
{
    assert HasNext(sch, p, n);
    var u :| n <= u && sch(u) == p;
    n' := n;

    while sch(n') != p && n' < u
    decreases u - n'
    invariant n' <= u
    invariant forall i :: n <= i <= n' ==> (t(i).pc[p] == t(n).pc[p] && t(i).flag[p] == t(n).flag[p])
    invariant forall i :: n <= i < n' ==> sch(i) != p
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
requires ValidProcess(p)
requires Valid(s)
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
    // Go to the position where p is scheduled
    n' := LemmaGetNextScheduledStep(p, t, sch, n);

    if(t(n').pc[p] == cs) {
        return;
    } 

    // Go to the position where p waits to enter the critical section
    while(t(n').pc[p] != a3a && t(n').pc[p] != a3b) 
    decreases distanceToCS(p, t(n'))
    invariant NextP(p, t(n'), t(n'+1))
    invariant Valid(t(n'))
    invariant t(n').pc[p] != cs
    {
        n' := LemmaGetNextScheduledStep(p, t, sch, n'+1);
    }

    if(ProcessIsBlockedInState(p, t(n'))) {
        n' := LemmaUnblocksEventually(t, n', p, sch);
        // At n', p is not blocked anymore.
        n' := LemmaGetNextScheduledStep(p, t, sch, n'); 
    }

    assert !ProcessIsBlockedInState(p, t(n')); 
    
    if(t(n').pc[p] == a3a && t(n').flag[Other(p)]) {
        assert t(n').turn == p;
        n' := LemmaGetNextScheduledStep(p, t, sch, n'+1);
    }             
    n' := n' + 1;
    assert t(n').pc[p] == cs;
}

lemma LemmaProcessIna3WhenBlocked(p: Process, t: Trace, sch: Schedule, n: nat, m: nat)
requires Valid(t(n))
requires Valid(t(m))
requires ValidProcess(p)
requires FairSchedule(sch)
requires IsTrace(t, sch)
requires ProcessIsBlockedInState(p, t(n))
requires t(n).pc[p] == a3a || t(n).pc[p] == a3b
requires n <= m
requires forall k :: n <= k < m ==> sch(k) == p
requires sch(m) == Other(p)
ensures forall k :: n <= k <= m ==> (t(k).pc[p] == a3a || t(k).pc[p] == a3b)
ensures forall k :: n <= k <= m ==> ProcessIsBlockedInState(p, t(k))
decreases m - n
{
    if(m == n) {
        // Thanks Dafny
    } else {
        if(t(n).pc[p] == a3a) {
            LemmaProcessIna3WhenBlocked(p, t, sch, n+1, m);
        } else {
            assert t(n+1).pc[p] == a3a;
            LemmaProcessIna3WhenBlocked(p, t, sch, n+1, m);
        }
    }
}

lemma LemmaUnblocksEventually(t: Trace, n: nat, p: Process, sch: Schedule) returns (n':nat)
requires Valid(t(n))
requires ValidProcess(p)
requires IsTrace(t, sch)
requires FairSchedule(sch)
requires t(n).pc[p] == a3a || t(n).pc[p] == a3b
requires ProcessIsBlockedInState(p, t(n))
ensures n <= n' 
ensures t(n').pc[p] == a3a || t(n').pc[p] == a3b
ensures !ProcessIsBlockedInState(p, t(n'))
{
    var q := Other(p);
    n' := LemmaGetNextScheduledStep(q, t, sch, n);
    LemmaProcessIna3WhenBlocked(p, t, sch, n, n');
    assert t(n').pc[p] == a3a || t(n').pc[p] == a3b;
    assert n <= n';
    assert t(n').flag[Other(p)];
    assert t(n').pc[q] != a1;

    if(t(n').pc[q] == a2 || t(n').pc[q] == a4) {
        n' := n' + 1;
        return;        
    }

    if(t(n').pc[q] == a3a) {
        n' := LemmaGetNextScheduledStep(q, t, sch, n');
        n' := n' + 1;
        assert t(n').pc[q] == a3b;       
    }

    if(t(n').pc[q] == a3b) {
        n' := LemmaGetNextScheduledStep(q, t, sch, n');
        n' := LemmaGetNextScheduledStep(q, t, sch, n' + 1);
        assert t(n').pc[q] == cs;       
    }

    if(t(n').pc[q] == cs) {
        var m := LemmaGetNextScheduledStep(q, t, sch, n'+1);
        LemmaProcessIna3WhenBlocked(p, t, sch, n'+1, m);
        assert t(m).pc[q] == a4;
        n' := m + 1;
    }
}