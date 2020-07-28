type Process(==)

datatype CState = Thinking | Hungry | Eating

class TicketSystem
{
var ticket: int
var serving: int
var cs: map<Process, CState>
var t: map<Process, int>

const P: set<Process>

predicate Valid()
reads this
{
    cs.Keys == t.Keys == P &&
    serving <= ticket && 
    (forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket) &&
    (forall p, q :: p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking ==> t[p] != t[q]) &&
    (forall p :: p in P && cs[p] == Eating ==> t[p] == serving)
}

constructor(processes: set<Process>) 
ensures Valid()
{
    P := processes;
    ticket, serving := 0, 0;
    cs := map p | p in processes :: Thinking;
    t := map p | p in processes :: 0;
}

method Request(p: Process)
requires Valid() && p in P && cs[p] == Thinking
modifies this
ensures Valid()
{
        t, ticket := t[p := ticket], ticket + 1; // Need to atomic increment feature of hardware t
        cs := cs[p := Hungry];
}

method Enter(p : Process)
requires Valid() && p in P && cs[p] == Hungry
modifies this
ensures Valid()
{
    if t[p] == serving {
        cs := cs[p := Eating];
    }
}

method Leave(p : Process) 
requires Valid() && p in P && cs[p] == Eating
modifies this
ensures Valid()
{
    // assert t[p] == serving;
    serving := serving + 1;
    cs := cs[p := Thinking];
}

lemma MutualExclusion(p: Process, q: Process)
requires Valid() && p in P && q in P
requires cs[p] == Eating && cs[q] == Eating
ensures p == q
{

}
}