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
    (forall p :: p in s.flag.Keys && ValidProcess(p)) &&
    (forall p :: p in s.pc.Keys && ValidProcess(p)) && 
    (forall p :: ValidProcess(p) && (s.pc[p] == cs <==> (s.flag[p] && s.turn == p))) 
}

predicate Init(s: State) {
    Valid(s) &&
    s.flag[0] == s.flag[1] == false &&
    s.turn == 0 &&
    s.pc[0] == a1 && s.pc[1] == a1
}

predicate Next(s: State, s': State) {
    Valid(s) &&
    exists p : Process :: ValidProcess(p) && NextP(p, s, s')
}

predicate NextP(p: Process, s: State, s': State)
requires Valid(s) && ValidProcess(p)
{
    (s.pc[p] == a1 && stmt_a1(p, s, s')) ||
    (s.pc[p] == a2 && stmt_a2(p, s, s')) ||
    (s.pc[p] == a3a && stmt_a3a(p, s, s')) ||
    (s.pc[p] == a3b && stmt_a3b(p, s, s')) ||
    (s.pc[p] == cs && stmt_cs(p, s, s')) ||
    (s.pc[p] == a4 && stmt_a4(p, s, s'))
}

predicate stmt_a1(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) && s.pc[p] == a1
{
    s'.flag == s.flag[p := true] &&
    s'.pc == s.pc[p := a2]
}

predicate stmt_a2(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) && s.pc[p] == a2
{
    s'.turn == Other(p) &&
    s'.pc == s.pc[p := a3a]
}

predicate stmt_a3a(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) && s.pc[p] == a3a
{
    (s.flag[Other(p)] && s'.pc == s.pc[p := a3b]) ||
    (!s.flag[Other(p)] && s'.pc == s.pc[p := cs])
}

predicate stmt_a3b(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) && s.pc[p] == a3b
{
    (s.turn == Other(p) && s'.pc == s.pc[p := a3a]) ||
    (s.turn != Other(p) && s'.pc == s.pc[p := cs])
}

predicate stmt_cs(p:Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) && s.pc[p] == cs
{
    s'.pc == s.pc[p := a4]
}

predicate stmt_a4(p: Process, s: State, s': State) 
requires ValidProcess(p) && Valid(s) && s.pc[p] == a4 
{
    s'.flag == s.flag[p := false] &&
    s'.pc == s.pc[p := a1]
}

// Mutual Exclusion
lemma MutualExclusion(s: State, p: Process, q: Process)
requires Valid(s) && ValidProcess(p) && ValidProcess(q)
requires s.pc[p] == cs && s.pc[q] == cs
ensures p == q
{

}