--------- MODULE pluscal_td6_1 --------
EXTENDS Integers,TLC
--------------------------------------------------------------

(*
--algorithm  cube  {
variables x=10,z=2*x,y=z+x;
{
l0:assert x=10 /\ y=z+x /\ z=2*x;
y:=z+x;
l1:assert x=10 /\ y=x+2*10;
}
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
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x=10 /\ y=z+x /\ z=2*x, 
                "Failure of assertion at line 9, column 4.")
      /\ y' = z+x
      /\ pc' = "l1"
      /\ UNCHANGED << x, z >>

l1 == /\ pc = "l1"
      /\ Assert(x=10 /\ y=x+2*10, 
                "Failure of assertion at line 11, column 4.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, z, y >>

Next == l0 \/ l1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

i ==
    /\ pc \in {"l0","l1","Done"}
    /\ x \in Int /\ y \in Int /\ z \in Int 
    /\ pc="l0" =>  x=10 /\ y=z+x /\ z=2*x
    /\ pc\in {"l1","Done"} =>  x=10 /\ y=x+2*10
   
Safetypc == pc\in {"Done"} =>  x=10 /\ y=x+2*10
=========
