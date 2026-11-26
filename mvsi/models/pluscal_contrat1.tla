---------------------- MODULE pluscal_contrat1  ------------------

EXTENDS Naturals, Integers, TLC

CONSTANTS x0,y0,z0,
        c0,r0

(*

--algorithm contrat1 {
  variables x=x0,c=c0,z=2*c, y= (z+1)*(z+1),r=r0;
{
    l1: assert x = 49 /\ z = 2*c /\ y = (z+1)*(z+1) /\ r = r0 /\ c=c0;
    y:= x+z+1;
    l2: assert x = 49 /\ z = 2*c /\ y =  (c+1)*(c+1) /\ r=0/\ c=c0;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b7f68c2d" /\ chksum(tla) = "2deccde2")
VARIABLES x, c, z, y, r, pc

vars == << x, c, z, y, r, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ c = c0
        /\ z = 2*c
        /\ y = (z+1)*(z+1)
        /\ r = r0
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x = 49 /\ z = 2*c /\ y = (z+1)*(z+1) /\ r = r0 /\ c=c0, 
                "Failure of assertion at line 13, column 9.")
      /\ y' = x+z+1
      /\ pc' = "l2"
      /\ UNCHANGED << x, c, z, r >>

l2 == /\ pc = "l2"
      /\ Assert(x = 49 /\ z = 2*c /\ y =  (c+1)*(c+1) /\ r=0/\ c=c0, 
                "Failure of assertion at line 15, column 9.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, c, z, y, r >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

========================================================
\* Modification History
\* Last modified Fri Feb 20 11:24:14 CET 2026 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
