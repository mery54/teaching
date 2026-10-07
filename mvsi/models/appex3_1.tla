--------------------- MODULE appex3_1 --------------------------------
EXTENDS Naturals, Integers, TLC
CONSTANTS x0,y0,z0,max,undef
min == -max
Z == min..max
P(x,y,z) == x \in Z /\ y \in Z /\ z \in Z
Q(x,y,z,xx,yy,zz) ==
		  /\ x \in Z /\ y \in Z /\ z \in Z
		  /\ xx \in Z /\ yy \in Z /\ zz \in Z
		  /\ xx = x +y+z /\ yy=y /\ zz=z

----------------------------------------
(* precondition *)
ASSUME x0 \in Z /\ y0 \in Z /\ z0 \in Z
----------------------------------------
(*
--algorithm appex3_1 {
  variables x=x0, 
            y = y0, 
            z=z0;
            
{
l0: assert x = x0  /\ y=y0 /\ z=z0 ;
    x := x+y+z;
l1: assert x = x0+y0+z0 /\ y=y0 /\ z=z0 ;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "346fb05e" /\ chksum(tla) = "d5fed099")
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ y = y0
        /\ z = z0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x = x0  /\ y=y0 /\ z=z0, 
                "Failure of assertion at line 23, column 5.")
      /\ x' = x+y+z
      /\ pc' = "l1"
      /\ UNCHANGED << y, z >>

l1 == /\ pc = "l1"
      /\ Assert(x = x0+y0+z0 /\ y=y0 /\ z=z0, 
                "Failure of assertion at line 25, column 5.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

------------------------------------------------
ISDEF(X,Y) == X # undef => X \in Y
DD(X) == X # undef => X \in min..max
------------------------------------------------
i ==
    /\ pc \in {"l0","l1","Done"}
    /\ ISDEF(x,Int)  /\ ISDEF(y,Int) /\ ISDEF(z,Int)
    /\ pc = "l0" => x = x0  /\ y=y0 /\ z=z0 
    /\ pc = "l1" => x = x0+y0+z0 /\ y=y0 /\ z=z0 
    /\ pc="Done" => Q(x0,y0,z0,x,y,z)

safetyrte ==DD(x) /\ DD(y) /\ DD(z)
safetypc == pc="Done" => Q(x0,y0,z0,x,y,z)
check == i /\ safetypc /\ safetyrte
==================================================================
