----------------------------- MODULE pluscal252 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS n

(*

--algorithm ex3{ 
variables x = 0;


process (one = n+1)
{
  A:   
    await x = n ;
  D:
    assert x=n;   
};

process (p \in 1..n)
{
  E:
    x := x + 1;
  
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "d5a0d28b" /\ chksum(tla) = "3597535f")
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {n+1} \cup (1..n)

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = n+1 -> "A"
                                        [] self \in 1..n -> "E"]

A == /\ pc[n+1] = "A"
     /\ x = n
     /\ pc' = [pc EXCEPT ![n+1] = "D"]
     /\ x' = x

D == /\ pc[n+1] = "D"
     /\ Assert(x=n, "Failure of assertion at line 16, column 5.")
     /\ pc' = [pc EXCEPT ![n+1] = "Done"]
     /\ x' = x

one == A \/ D

E(self) == /\ pc[self] = "E"
           /\ x' = x + 1
           /\ pc' = [pc EXCEPT ![self] = "Done"]

p(self) == E(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one
           \/ (\E self \in 1..n: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 




====
