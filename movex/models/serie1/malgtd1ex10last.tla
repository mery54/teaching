-------------------------------- MODULE malgtd1ex10last --------------------------------

EXTENDS Naturals, Integers,TLC
CONSTANTS x0,y0,z0,UND
VARIABLES  x,y,z,pc

-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
pre == /\ x0 \in Int /\ y0 \in Int 
       /\  x0=11 /\ y0=13 /\ z0 = UND
  ------------------------------------------------------------------------------
(* Interpretation: w assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)
ASSUME  pre
       
---------------------------------------------------------------------
(* Action for transitioon of the algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ z'=x
    /\ x' = z
    /\ y' = z'

---------------------------------------------------------------
(* Computations *)
Next == al1l2  \/ UNCHANGED <<x,y,z,pc>>
Init == pc="l1" /\ x=x0 /\ y =y0  /\ z = z0 /\ pre
----------------------
(* Checking the annotation by checking the invariant i derived from the annotation *)
i ==
    /\ pc="l1" =>  x=x0 /\ y=y0 /\ pre
    /\ pc="l2" =>  x=26 \div 2  /\ y = 33 \div 3 

safe ==  i

=============================================================================
\* Modification History
\* Last modified Wed Feb 23 08:31:14 CET 2022 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
