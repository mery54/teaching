--------------------------- MODULE pluscal_exapp2 ---------------------------

EXTENDS Naturals, Integers, TLC

CONSTANTS mini,maxi
(*
--algorithm  ex1{
variables   u=5;
            v=u+7;
{
  l1: assert u=5 /\ v=u+7; 
  u:=u+v+5;
  l2: assert u+v= 22;
  v:=v+u;
  l3: assert u+v = 24;
  skip;
}
}
*)
\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = 5
        /\ v = u+7
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(u=5 /\ v=u+7, "Failure of assertion at line 11, column 7.")
      /\ u' = u+v+5
      /\ pc' = "l2"
      /\ v' = v

l2 == /\ pc = "l2"
      /\ Assert(u+v= 22, "Failure of assertion at line 13, column 7.")
      /\ v' = v+u
      /\ pc' = "l3"
      /\ u' = u

l3 == /\ pc = "l3"
      /\ Assert(u+v = 24, "Failure of assertion at line 15, column 7.")
      /\ TRUE
      /\ pc' = "Done"
      /\ UNCHANGED << u, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2 \/ l3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



inv ==
    /\ pc = "l1" => u=5 /\ v=u+7
    /\ pc = "l2" => u+v= 22
    /\ pc = "l3" => u+v = 24


rte  == u \in mini..maxi /\ v \in mini..maxi
=============================================================================
\* Modification History
\* Last modified Thu Nov 26 15:27:39 CET 2020 by mery
\* Created Thu Nov 26 12:39:01 CET 2020 by mery
