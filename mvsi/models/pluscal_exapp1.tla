--------------------------- MODULE pluscal_exapp1 ---------------------------

EXTENDS Naturals, Integers, TLC

CONSTANTS mini,maxi
(*
--algorithm  ex1{
variables   u=5;
            v=u+7;
{
  l1: u:=u+v+5;
  l2: v:=v+u;
  l3: skip;
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
      /\ u' = u+v+5
      /\ pc' = "l2"
      /\ v' = v

l2 == /\ pc = "l2"
      /\ v' = v+u
      /\ pc' = "l3"
      /\ u' = u

l3 == /\ pc = "l3"
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
    /\ pc = "l1" => u=5 /\ v=12
    /\ pc = "l2" => u=22 /\ v=12
    /\ pc = "l3" => u=22 /\ v= 34


inv1 ==
    /\ pc = "l1" => u=5 /\ v=u+7
    /\ pc = "l2" => u+v= 22
    /\ pc = "l3" => u+v = 24


rte  == u \in mini..maxi /\ v \in mini..maxi
=============================================================================
\* Modification History
\* Last modified Thu Nov 26 15:22:57 CET 2020 by mery
\* Created Thu Nov 26 12:39:01 CET 2020 by mery
