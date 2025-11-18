---------------------- MODULE appex4_13bis --------------------------------
EXTENDS Naturals, Integers, TLC

(*
--algorithm  test{
variables x=1,y=12;
{
 
  l1:assert x=1 /\ y=12;
  x:=2*y;
  l2: assert x=1 /\ y= 24; 
}
}

*)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 1
        /\ y = 12
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=1 /\ y=12, "Failure of assertion at line 9, column 6.")
      /\ x' = 2*y
      /\ pc' = "l2"
      /\ y' = y

l2 == /\ pc = "l2"
      /\ Assert(x=1 /\ y= 24, "Failure of assertion at line 11, column 7.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

test == pc # "Done"

===============
