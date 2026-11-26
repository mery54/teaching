----------------------------- MODULE  pluscalappaspd5-----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*
--wf
--algorithm ex3{ 
variables x = 0, y = 8;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
      assert  ((x = 1  \/ x=0 \/ x=2)  /\(y = 5 \/  y= 6 \/  y=7 \/ y = 8 \/ y=9));
};  (* assert A1 *)

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
   assert ((x = 1  \/ x=2) /\  (y=7 \/y=8 \/ y=9 \/ y=10));
   (*assert A2 *) 
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7b5fc7e" /\ chksum(tla) = "3c965cc5")
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 8
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
     /\ Assert(((x = 1  \/ x=0 \/ x=2)  /\(y = 5 \/  y= 6 \/  y=7 \/ y = 8 \/ y=9)), 
               "Failure of assertion at line 18, column 7.")
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
     /\ Assert(((x' = 1  \/ x'=2) /\  (y=7 \/y=8 \/ y=9 \/ y=10)), 
               "Failure of assertion at line 29, column 4.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ y' = y

two == D \/ E \/ F

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
