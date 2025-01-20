-------------------------------- MODULE malgtd1ex10ter --------------------------------

EXTENDS Naturals, Integers,TLC
CONSTANTS x0,y0
VARIABLES  x,y,pc
------------------------------------------------------------------------------
(* Interpretation: w assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)
ASSUME /\ x0 \in Int /\ y0 \in Int 
       /\  x0=1 /\ y0=12
-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
pre == /\ x0 \in Int /\ y0 \in Int 
       /\  x0=1 /\ y0=12
---------------------------------------------------------------------
(* Action for transitioon of the algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'=2*y+x
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
    /\ pc="l2" =>  x=25 /\ y =  y0 /\ PrintT(x)

safe ==  i

=============================================================================
\* Modification History
\* Last modified Wed Mar 06 10:41:19 CET 2024 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
