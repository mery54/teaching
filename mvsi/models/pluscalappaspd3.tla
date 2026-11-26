----------------------------- MODULE pluscalappaspd3 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex3{ 
variables x = 0, y = 2;


process (one = 1)
variable u;
{
  A:
  u := x+1;
  AB:
    x := u;
  B: 
    y := y -1;  
  C:
 assert x=1 /\ y=1 \/ x=0/\y=1 \/  

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
  G:
    assert
};

}
end algorithm; 

*)


\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, pc, u

vars == << x, y, pc, u >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 2
        (* Process one *)
        /\ u = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "D"]

A == /\ pc[1] = "A"
     /\ u' = x+1
     /\ pc' = [pc EXCEPT ![1] = "AB"]
     /\ UNCHANGED << x, y >>

AB == /\ pc[1] = "AB"
      /\ x' = u
      /\ pc' = [pc EXCEPT ![1] = "B"]
      /\ UNCHANGED << y, u >>

B == /\ pc[1] = "B"
     /\ y' = y -1
     /\ pc' = [pc EXCEPT ![1] = "C"]
     /\ UNCHANGED << x, u >>

C == /\ pc[1] = "C"
     /\ Assert((x=0 \/ x = 1 \/  x = 2 \/ x=3) /\ (y=1 \/  y = 3 \/ y = 4), 
               "Failure of assertion at line 19, column 2.")
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << x, y, u >>

one == A \/ AB \/ B \/ C

D == /\ pc[2] = "D"
     /\ x' = x - 1
     /\ pc' = [pc EXCEPT ![2] = "E"]
     /\ UNCHANGED << y, u >>

E == /\ pc[2] = "E"
     /\ y' = y+2
     /\ pc' = [pc EXCEPT ![2] = "F"]
     /\ UNCHANGED << x, u >>

F == /\ pc[2] = "F"
     /\ x' = x+2
     /\ pc' = [pc EXCEPT ![2] = "G"]
     /\ UNCHANGED << y, u >>

G == /\ pc[2] = "G"
     /\ Assert((x= 0 \/ x = 1 \/  x = 2 \/ x=3) /\ (y = 3 \/ y = 4), 
               "Failure of assertion at line 31, column 5.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << x, y, u >>

two == D \/ E \/ F \/ G

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



\* (x=0 \/ x = 1 \/  x = 2 \/ x=3) /\ (y=1 \/  y = 3 \/ y = 4); 

\*  (x= 0 \/ x = 1 \/  x = 2 \/ x=3) /\ (y = 3 \/ y = 4)


====
