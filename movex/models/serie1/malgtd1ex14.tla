-------------------------------- MODULE malgtd1ex14 --------------------------------

EXTENDS Naturals, Integers,TLC
CONSTANTS x0,y0,z0,c0,r0
VARIABLES  x,y,z,c,r,pc

vars == <<x,y,z,c,r,pc>>
------------------------------------------------------------------------------
(* Interpretation: w assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)

ASSUME x0 \in Int /\ y0 \in Int /\ z0 \in Int  /\ c0 \in Int /\ r0 \in Int /\  r0 = 0
-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
requires ==  x0 \in Int /\ y0 \in Int /\ z0 \in Int  /\ c0 \in Int /\ r0 \in Int /\  r0 = 0

---------------------------------------------------------------------
(* Action for transitioon of the algorithm *)
al0l1 ==
    /\ pc="l0"
    /\ pc'="l1"
    /\ x'= 49
    /\ y'=  (2*c+1)*(2*c+1)
    /\ z'=2*c
    /\ c'=c
    /\ r'=r

al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'= 49
    /\ y'=  x+z+1
    /\ z'=z
    /\ c'=c
    /\ r'=r



---------------------------------------------------------------
(* Computations *)
Next == al0l1 \/ al1l2  \/ UNCHANGED vars
Init == pc="l0" /\ x=x0 /\ y =y0  /\ z=z0 /\ /\ r=r0 /\ c=c0 /\  requires
----------------------
(* Checking the annotation by checking the invariant i derived from the annotation *)
i ==
    /\ typeInt(x) /\ typeInt(y) /\ typeInt(z) /\ typeInt(c) /\ typeInt(r)   
    /\ pc="l0" =>  x=x0 /\ y=y0 /\  z=z0 /\ r=r0 /\  c=c0 /\ requires
    /\ pc="l1" =>  x=49 /\ z=2*c /\ y = (z+1)*(z+1) /\ requires
    /\ pc="l2" =>  x=49 /\ z=2*c /\ y = (c+1)*(c+1) /\ requires

=============================================================================
\* Modification History
\* Last modified Mon Mar 11 11:17:42 CET 2024 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
