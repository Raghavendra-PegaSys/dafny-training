type Process(==)
const P: set<Process>
datatype CState = Thinking | Hungry | Eating

datatype TSState = TSState(ticket: int, serving: int, cs: map<Process, CState>, t: map<Process, int>)

predicate Valid(s: TSState)
{
    s.cs.Keys == s.t.Keys == P &&
    s.serving <= s.ticket &&
    (forall p :: p in P && s.cs[p] != Thinking ==> s.serving <= s.t[p] < s.ticket) &&
    (forall p, q :: p in P && q in P && p != q && s.cs[p] != Thinking && s.cs[q] != Thinking ==> s.t[p] != s.t[q]) &&
    (forall p :: p in P && s.cs[p] == Eating ==> s.t[p] == s.serving) &&
    (forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s, i))
}

lemma MutualExclusion(s: TSState, p: Process, q: Process)
requires Valid(s) && p in P && q in P
requires s.cs[p] == Eating && s.cs[q]  == Eating 
ensures  p == q
{
    // Thanks Dafny
}

// For Liveness

predicate Init(s: TSState) {
    s.cs.Keys == s.t.Keys == P &&
    s.ticket == s.serving &&
    forall p :: p in P ==> s.cs[p] == Thinking
}

predicate Next(s: TSState, s' : TSState) {
    Valid(s) &&
    exists p :: p in P && NextP(s, p, s')
}

predicate NextP(s: TSState, p: Process, s':TSState) 
requires Valid(s) && p in P
{
    Request(s, p, s') || Enter(s, p, s') || Leave(s, p, s')
}

predicate Request(s: TSState, p: Process, s': TSState)
requires p in P && Valid(s)
{
    s.cs[p] == Thinking && s'.cs == s.cs[p := Hungry] && 
    s'.ticket == s.ticket + 1 && 
    s'.serving == s.serving &&
    s'.t == s.t[p := s.ticket]
}

predicate Enter(s: TSState, p: Process, s': TSState)
requires p in P && Valid(s)
{
    s.cs[p] == Hungry && 
    ((s.t[p] == s.serving && s'.cs == s.cs[p := Eating]) || (s.t[p] != s.serving && s'.cs == s.cs)) &&
    s'.ticket == s.ticket &&
    s'.serving == s.serving && 
    s'.t == s.t
}

predicate Leave(s: TSState, p: Process, s':TSState)
requires p in P && Valid(s)
{
    s.cs[p] == Eating && s'.cs == s.cs[p := Thinking] &&
    s.t == s'.t &&
    s.ticket == s'.ticket &&
    s.serving + 1 == s'.serving

}

type Schedule = nat -> Process

predicate IsSchedule(sch: Schedule) {
    forall i :: sch(i) in P
}

predicate FairSchedule(sch: Schedule) {
    IsSchedule(sch) &&
    forall p, n :: p in P ==> HasNext(sch, p, n)
}

predicate HasNext(sch: Schedule, p : Process, n: nat) {
    exists n' :: n <= n' && sch(n') == p
}

type Trace = nat -> TSState

predicate IsTrace(t: Trace, sch: Schedule) 
requires IsSchedule(sch)
{
    Init(t(0)) && 
    forall i : nat :: Valid(t(i)) && NextP(t(i), sch(i), t(i+1))
}

predicate TicketIsInUse(s: TSState, i : int)
requires s.cs.Keys == s.t.Keys == P
{
    exists p :: p in P && s.cs[p] != Thinking && s.t[p] == i
}

function CurrentlyServedProcess(s: TSState) : Process
requires Valid(s) && (exists p :: p in P && s.cs[p] == Hungry)
{
    assert TicketIsInUse(s, s.serving);
    var q :| q in P && s.cs[q] != Thinking && s.t[q] == s.serving;
    q
}

lemma GetNextStep(trace: Trace, sch: Schedule, p: Process, n: nat) returns (n': nat)
requires FairSchedule(sch) && IsTrace(trace, sch) && p in P 
requires trace(n).cs[p] != Thinking && trace(n).t[p] == trace(n).serving
ensures n <= n' && sch(n') == p
ensures trace(n').serving == trace(n).serving && trace(n').cs[p] == trace(n).cs[p] && trace(n').t[p] == trace(n).t[p]
ensures forall q :: q in P && trace(n).cs[q] == Hungry ==> trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q]
{
    assert HasNext(sch, p, n);
    var u :| n <= u && sch(u) == p;
    // Why not n' be u? Ans: n' won't be the smallest u. Not Constructive. And we do not know that all the other properties we want holds till n'
    n' := n;

    while sch(n') != p 
    invariant n' <= u
    invariant trace(n').serving == trace(n).serving && trace(n').cs[p] == trace(n).cs[p] && trace(n').t[p] == trace(n).t[p]
    invariant forall q :: q in P && trace(n).cs[q] == Hungry ==> trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q]
    decreases u - n'
    {
        n' := n' + 1;
    }
}

 // Main Liveness theorem
lemma Liveness(trace: Trace, sch: Schedule, p: Process, n: nat) returns (n':nat )
requires FairSchedule(sch) && IsTrace(trace, sch) && p in P && trace(n).cs[p] == Hungry
ensures n <= n' && trace(n').cs[p] == Eating
{
    n' := n;
    while true
    invariant n <= n' && trace(n').cs[p] == Hungry
    decreases trace(n').t[p] - trace(n').serving
    {
        var q := CurrentlyServedProcess(trace(n'));
        if trace(n').cs[q] == Hungry {
            n' := GetNextStep(trace, sch, q, n');
            n' := n' + 1;
            if p == q {
                return;
            }
        }
        n' := GetNextStep(trace, sch, q, n');
        n' := n' + 1;
    }
}