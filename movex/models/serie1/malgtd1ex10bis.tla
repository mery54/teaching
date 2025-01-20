-------------------------------- MODULE malgtd1ex10bis --------------------------------

EXTENDS Naturals, Integers,TLC
CONSTANTS x0,y0
VARIABLES  x,y,pc
------------------------------------------------------------------------------
(* Interpretation: w assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)
ASSUME /\ x0 \in Int /\ y0 \in Int 
       /\  x0=2^4 /\ y0=2 /\ x0*y0=2^5
-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
pre == /\ x0 \in Int /\ y0 \in Int 
       /\  x0=2^4 /\ y0=2 /\ x0*y0=2^5
---------------------------------------------------------------------
(* Action for transitioon of the algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'=y+x+2^x
    /\ y'=y
---------------------------------------------------------------
(* Computations *)
Next == al1l2  \/ UNCHANGED <<x,y,pc>>
Init == pc="l1" /\ x=x0 /\ y =y0  /\ pre
----------------------
(* Checking the annotation by checking the invariant i derived from the annotation *)
i ==
    /\ typeInt(x) /\ typeInt(y) 
    /\ pc="l1" =>  x=x0 /\ y=y0 /\ pre
    /\ pc="l2" =>  x=2^10 /\ y = 2 /\ PrintT(x)

safe ==  i

=============================================================================
\* Modification History
\* Last modified Tue Feb 07 11:35:34 CET 2023 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
