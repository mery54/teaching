----------------------------- MODULE pluscalappaspd1 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex1{ 
variables x = 1;


process (one = 1)
{
  A:
    x := x - 1;
};

process (two = 2)
{
  C:
    x := x + 1;
  D:
    assert x=1 \/ x=2;
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 1
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "C"]

A == /\ pc[1] = "A"
     /\ x' = x - 1
     /\ pc' = [pc EXCEPT ![1] = "Done"]

one == A

C == /\ pc[2] = "C"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![2] = "D"]

D == /\ pc[2] = "D"
     /\ Assert(x=1 \/ x=2, "Failure of assertion at line 20, column 5.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ x' = x

two == C \/ D

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION






====
