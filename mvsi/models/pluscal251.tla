----------------------------- MODULE pluscal251 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*

--algorithm ex3{ 
variables x = 0, y = 2;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
    await x = 2 ;
  D:
    assert x=2;   
};

process (two = 2)
{
  E:
    x := x + 1;
  F:
    y:=y-1;   
  G:
    await y = 0 ;
  H:
     assert y = 0
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "a38de460" /\ chksum(tla) = "c3d7545b")
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 2
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "E"]

A == /\ pc[1] = "A"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![1] = "B"]
     /\ y' = y

B == /\ pc[1] = "B"
     /\ y' = y -1
     /\ pc' = [pc EXCEPT ![1] = "C"]
     /\ x' = x

C == /\ pc[1] = "C"
     /\ x = 2
     /\ pc' = [pc EXCEPT ![1] = "D"]
     /\ UNCHANGED << x, y >>

D == /\ pc[1] = "D"
     /\ Assert(x=2, "Failure of assertion at line 20, column 5.")
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << x, y >>

one == A \/ B \/ C \/ D

E == /\ pc[2] = "E"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![2] = "F"]
     /\ y' = y

F == /\ pc[2] = "F"
     /\ y' = y-1
     /\ pc' = [pc EXCEPT ![2] = "G"]
     /\ x' = x

G == /\ pc[2] = "G"
     /\ y = 0
     /\ pc' = [pc EXCEPT ![2] = "H"]
     /\ UNCHANGED << x, y >>

H == /\ pc[2] = "H"
     /\ Assert(y = 0, "Failure of assertion at line 32, column 6.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << x, y >>

two == E \/ F \/ G \/ H

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

  i == (pc[1]# "Done" \/ pc[2]#"Done") 


====
