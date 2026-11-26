-------------------------------- MODULE pluscal3 --------------------------------
EXTENDS TLC, Integers, Naturals, Reals

(*
--algorithm ex1 {
variables x,y,u;
{
init:x:=1;y:=12;u:=3;
l1:x:=2*y;
assert y \geq 12;
print(<<x,y>>);
}
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, u, pc

vars == << x, y, u, pc >>

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ y = defaultInitValue
        /\ u = defaultInitValue
        /\ pc = "init"

init == /\ pc = "init"
        /\ x' = 1
        /\ y' = 12
        /\ u' = 3
        /\ pc' = "l1"

l1 == /\ pc = "l1"
      /\ x' = 2*y
      /\ Assert(y \geq 12, "Failure of assertion at line 10, column 1.")
      /\ PrintT((<<x',y>>))
      /\ pc' = "Done"
      /\ UNCHANGED << y, u >>

Next == init \/ l1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

i == 
    /\ pc="l1" => x=1/\y=12
    /\ pc="Done" => x=1 /\ y=24


=============================================================================
\* Modification History
\* Last modified Sun Oct 02 23:32:31 CEST 2016 by mery
\* Created Wed Nov 18 16:12:05 CET 2015 by mery
