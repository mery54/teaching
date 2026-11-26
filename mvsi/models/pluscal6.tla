------------------------------ MODULE pluscal6 ------------------------------
EXTENDS TLC, Integers, Naturals

(*

--algorithm ex3 {
variables x,y,z;
{
init:x:=10;z:=2*x;y:=z+x;
l1:y:=z+x;
l2:print <<x,y,z>>;
}
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ y = defaultInitValue
        /\ z = defaultInitValue
        /\ pc = "init"

init == /\ pc = "init"
        /\ x' = 10
        /\ z' = 2*x'
        /\ y' = z'+x'
        /\ pc' = "l1"

l1 == /\ pc = "l1"
      /\ y' = z+x
      /\ pc' = "l2"
      /\ UNCHANGED << x, z >>

l2 == /\ pc = "l2"
      /\ PrintT(<<x,y,z>>)
      /\ pc' = "Done"
      /\ UNCHANGED << x, y, z >>

Next == init \/ l1 \/ l2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

safetypc == pc="l2" => x=10 /\ y=x+2*10
safety == safetypc

=============================================================================
\* Modification History
\* Last modified Mon Dec 12 10:58:43 CET 2016 by mery
\* Created Wed Nov 18 15:48:54 CET 2015 by mery
