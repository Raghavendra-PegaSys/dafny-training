type Value = set<nat>
type Process = nat
datatype State = State(chosen: map<Process, Value>)

predicate ValidProcess(p: Process) {
    true
}

predicate Valid(s: State) {
    && (forall p :: p in s.chosen.Keys && ValidProcess(p))
    && (forall p :: ValidProcess(p) && |s.chosen[p]| <= 1)
}

predicate Init(s: State) {
    && Valid(s)
    && forall p:Process :: ValidProcess(p) && s.chosen[p] == {}
}

predicate NextP(p: Process, s: State, s': State) 
requires Valid(s) 
requires ValidProcess(p)
{
    && (s.chosen[p] == {})
    && (forall q :: q in s'.chosen.Keys && ValidProcess(q))
    && (forall q :: q != p && ValidProcess(q) && s'.chosen[q] == s.chosen[q])
    && (|s'.chosen[p]| == 1)
}

predicate Next(s: State, s': State)
requires Valid(s) 
{
    exists p : Process :: ValidProcess(p) && NextP(p, s, s')
}

lemma InductiveInvariance(s: State, s': State)
requires Valid(s)
requires Next(s, s')
ensures Valid(s)
{
    // Thanks Dafny
}

// Liveness
type Schedule = nat -> Process

predicate IsSchedule(sch: Schedule) {
    forall i :: ValidProcess(sch(i))
}

predicate FairSchedule(sch: Schedule) 
{
    && IsSchedule(sch)
    && forall p, n :: ValidProcess(p) && HasNext(sch, p, n)
}

predicate HasNext(sch: Schedule, p : Process, n: nat) 
requires ValidProcess(p)
{
    exists n' :: n <= n' && sch(n') == p
}

type Trace = nat -> State

predicate IsTrace(t: Trace, sch: Schedule) 
{
    && Init(t(0))
    && forall i : nat :: Valid(t(i)) && NextP(sch(i), t(i), t(i+1))
}

lemma GetNextScheduledStep(sch: Schedule, t: Trace, p: Process, n: nat) returns (n':nat)
requires ValidProcess(p)
requires FairSchedule(sch)
requires IsTrace(t, sch)
ensures n <= n' && sch(n') == p
ensures forall i :: n <= i <= n' ==> t(i).chosen[p] == t(n).chosen[p] 
{
    assert HasNext(sch, p, n);
    var u :| n <=u && sch(u) == p;
    n' := n;

    while sch(n') != p && n' < u
    decreases u - n'
    invariant n' <= u
    invariant forall i :: n <= i <= n' ==> (t(i).chosen[p] == t(n).chosen[p])
    invariant forall i :: n <= i < n' ==> sch(i) != p
    {
        n' := n' + 1;
        assert t(n').chosen[p] == t(n).chosen[p];
    }
}

lemma Liveness(sch: Schedule, t: Trace, p: Process, n: nat) returns (n':nat) 
requires ValidProcess(p)
requires FairSchedule(sch)
requires IsTrace(t, sch)
ensures n <= n' && (ValidProcess(p) ==> t(n').chosen[p] != {})
{
    n' := n;

    assert Valid(t(n'));

    if(t(n').chosen[p] != {}) {
        return;
    }

    n' := GetNextScheduledStep(sch, t, p, n);
    assert |t(n').chosen[p]| == 0;
    assert NextP(p, t(n'), t(n'+1));

    n' := n' + 1;
    assert |t(n').chosen[p]| == 1;
}