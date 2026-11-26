----------  MODULE pluscalcours2 -----
EXTENDS Integers, TLC
-----------------------
(*
--algorithm ExMacro
variables x = 0;

macro incrX()
begin
  x := x + 1;
end macro;

begin
  l0:assert (x = 0);
  l1:incrX();
  l2:incrX();
  l3:assert (x = 2);
  
end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7a44a66d" /\ chksum(tla) = "16fc2c29")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert((x = 0), "Failure of assertion at line 14, column 6.")
      /\ pc' = "l1"
      /\ x' = x

l1 == /\ pc = "l1"
      /\ x' = x + 1
      /\ pc' = "l2"

l2 == /\ pc = "l2"
      /\ x' = x + 1
      /\ pc' = "l3"

l3 == /\ pc = "l3"
      /\ Assert((x = 2), "Failure of assertion at line 17, column 6.")
      /\ pc' = "Done"
      /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
================
