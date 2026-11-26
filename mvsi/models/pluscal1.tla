------------------------------ MODULE pluscal1 ------------------------------
EXTENDS TLC, Integers, Naturals

(*
--fair algorithm ex1 {
variables x=10,z=2*x,y=z+x;
{
l1:y:=z+x;
l2:print <<x,y,z>>;
}
}
*)
\* BEGIN TRANSLATION
VARIABLES x, z, y, pc

vars == << x, z, y, pc >>

Init == (* Global variables *)
        /\ x = 10
        /\ z = 2*x
        /\ y = z+x
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ y' = z+x
      /\ pc' = "l2"
      /\ UNCHANGED << x, z >>

l2 == /\ pc = "l2"
      /\ PrintT(<<x,y,z>>)
      /\ pc' = "Done"
      /\ UNCHANGED << x, z, y >>

Next == l1 \/ l2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


MIN == -32768
MAX == 32767
D == MIN..MAX

i == 
    /\ pc \in {"l1","l2","Done"}
    /\ pc="l1" => x=10/\ y=z+x /\ z=2*x
    /\ pc="l2"  => x=10 /\ y=x+2*10
    
    
safetypc == pc="Done" => x=10 /\ y=x+2*10
safety == i

=============================================================================
\* Modification History
\* Last modified Mon Dec 03 17:05:05 CET 2018 by mery
\* Created Wed Nov 18 15:48:54 CET 2015 by mery
