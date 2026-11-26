----------------------------- MODULE pluscalil265 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex1{ 
variables x = 5;


process (one = 1)
variables u;
{
  A:
    u := x-1;
  AB:  
    x := u;
  B: 
    x := x -2;   
};

process (two = 2)
{
  C:
    x := x + 3;
  D:
    assert  x \in {2,4,5,7,8};
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "6035963" /\ chksum(tla) = "6af87ce9")
CONSTANT defaultInitValue
VARIABLES x, pc, u

vars == << x, pc, u >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 5
        (* Process one *)
        /\ u = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "C"]

A == /\ pc[1] = "A"
     /\ u' = x-1
     /\ pc' = [pc EXCEPT ![1] = "AB"]
     /\ x' = x

AB == /\ pc[1] = "AB"
      /\ x' = u
      /\ pc' = [pc EXCEPT ![1] = "B"]
      /\ u' = u

B == /\ pc[1] = "B"
     /\ x' = x -2
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ u' = u

one == A \/ AB \/ B

C == /\ pc[2] = "C"
     /\ x' = x + 3
     /\ pc' = [pc EXCEPT ![2] = "D"]
     /\ u' = u

D == /\ pc[2] = "D"
     /\ Assert(x \in {2,4,5,7,8}, 
               "Failure of assertion at line 25, column 5.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << x, u >>

two == C \/ D

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") =>  x \in 0..8
Safe2 ==    (\A self \in ProcSet: pc[self] = "Done") => x \in 3..8
Safe == Safe2
==============
