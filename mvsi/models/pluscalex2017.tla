---------------------- MODULE pluscalex2017 --------------------------------
EXTENDS Naturals, Integers, TLC



(*
--fair algorithm ex {
  variables  u = 3; 
             v = u+4;
{
    l1: u:=u+v+7;
    l2: v:=v+u;
    l3: skip;
}

}
*)
\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = 3
        /\ v = u+4
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ PrintT(<<u,v>>)
      /\ pc' = "l1"
      /\ UNCHANGED << u, v >>

l1 == /\ pc = "l1"
      /\ u' = u+v+7
      /\ pc' = "l2"
      /\ v' = v

l2 == /\ pc = "l2"
      /\ v' = v+u
      /\ pc' = "l9"
      /\ u' = u

l9 == /\ pc = "l9"
      /\ PrintT(<<u, v>>)
      /\ pc' = "Done"
      /\ UNCHANGED << u, v >>

Next == l0 \/ l1 \/ l2 \/ l9
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


i == 
    /\ pc="l1" => u=3 /\ v=u+4
    /\ pc="l2" => u+v=24
    /\ pc="l3" => 2*u+v=58
    
stop == pc # "Done"


==================================================================
\* Modification History
\* Last modified Wed Dec 13 22:12:26 CET 2017 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
