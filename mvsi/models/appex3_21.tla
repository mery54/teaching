--------------------- MODULE appex3_21 --------------------------------
EXTENDS Naturals, Integers, TLC
CONSTANTS x0,y0,z0,max,undef
min == -max
Z == min..max
P(x,y,z) == x= 10 /\  y = z+x /\ z=2*x
Q(x,y,z,xx,yy,zz) ==
		  /\ x= 10 /\  y = z+x /\ z=2*x
		  /\ xx= 10 /\ yy = xx+2*10
----------------------------------------
(* precondition *)
ASSUME P(x0,y0,z0)
----------------------------------------
(*
--algorithm appex3_21 {
  variables x=x0, 
            y = y0, 
            z=z0;
            
{
l0: assert x= 10 /\  y = z+x /\ z=2*x; 
    y := z+x;
l1: assert x= 10 /\ y = x+2*10 ;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "218092e6" /\ chksum(tla) = "a768c50f")
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ y = y0
        /\ z = z0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x= 10 /\  y = z+x /\ z=2*x, 
                "Failure of assertion at line 21, column 5.")
      /\ y' = z+x
      /\ pc' = "l1"
      /\ UNCHANGED << x, z >>

l1 == /\ pc = "l1"
      /\ Assert(x= 10 /\ y = x+2*10, 
                "Failure of assertion at line 23, column 5.")
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
    /\ pc = "l0" => x= 10 /\  y = z+x /\ z=2*x 
    /\ pc = "l1" =>  x= 10 /\ y = x+2*10 

safetyrte ==DD(x) /\ DD(y) /\ DD(z)
safetypc == pc="Done" => Q(x0,y0,z0,x,y,z)
check == i /\ safetypc /\ safetyrte
==================================================================
