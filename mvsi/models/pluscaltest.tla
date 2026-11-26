------------------------------ MODULE pluscaltest ------------------------------
EXTENDS TLC, Integers, Naturals
CONSTANTS c
(*
--algorithm ex1 {
variables x=c,y=3-c,z=c+2;
{
z:=x+y+2*z;
z:= x;
y:=7;
x:=0;
}
}
*)
\* BEGIN TRANSLATION
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = c
        /\ y = 3-c
        /\ z = c+2
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ z' = x+y+2*z
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << x, y >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ z' = x
         /\ y' = 7
         /\ x' = 0
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

MIN == -32768
MAX == 32767
D == MIN..MAX

i == 
    /\ pc \in {"l1","l2","Done"}
    /\ pc="l1" => x+y=3 /\ z = x+2
    /\ pc="l2"  => x+y=3 /\ z+y = x+z
    
    


=============================================================================
\* Modification History
\* Last modified Thu Mar 03 11:49:19 CET 2022 by mery
\* Created Wed Nov 18 15:48:54 CET 2015 by mery
