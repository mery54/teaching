---------------------------- MODULE pluscalil267 ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*
--algorithm ex1{ 
variables x = 1, y = 2;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
      assert  x \in {1,2,3} /\ y \in {1,2,3};
};

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
    
    G:assert  x \in {2,3} /\ y \in {3,4};
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "fe81b067" /\ chksum(tla) = "490a009c")
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 1
        /\ y = 2
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "D"]

A == /\ pc[1] = "A"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![1] = "B"]
     /\ y' = y

B == /\ pc[1] = "B"
     /\ y' = y -1
     /\ pc' = [pc EXCEPT ![1] = "C"]
     /\ x' = x

C == /\ pc[1] = "C"
     /\ Assert(x \in {1,2,3} /\ y \in {1,2,3}, 
               "Failure of assertion at line 17, column 7.")
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << x, y >>

one == A \/ B \/ C

D == /\ pc[2] = "D"
     /\ x' = x - 1
     /\ pc' = [pc EXCEPT ![2] = "E"]
     /\ y' = y

E == /\ pc[2] = "E"
     /\ y' = y+2
     /\ pc' = [pc EXCEPT ![2] = "F"]
     /\ x' = x

F == /\ pc[2] = "F"
     /\ x' = x+2
     /\ pc' = [pc EXCEPT ![2] = "G"]
     /\ y' = y

G == /\ pc[2] = "G"
     /\ Assert(x \in {2,3} /\ y \in {3,4}, 
               "Failure of assertion at line 29, column 7.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << x, y >>

two == D \/ E \/ F \/ G

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") => x \in {3} /\ y \in {3}
Safe == Safe1

==================


=============================================================================
\* Modification History
\* Last modified Wed Apr 29 18:19:08 CEST 2026 by mery
\* Created Wed Apr 29 16:43:28 CEST 2026 by mery
