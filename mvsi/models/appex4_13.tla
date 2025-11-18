-------------------------------- MODULE appex4_13 --------------------------------
EXTENDS Naturals

VARIABLES  x,y,pc
---------------------------------------------------------------------
(* Define actions from the text of annotated algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'=2*y
    /\ y'=y
---------------------------------------------------------------------    
(*  Define  the computation relation *)
next == al1l2  \/ UNCHANGED <<x,y,pc>>
(* Define the initial conditions *)
init == pc="l1" /\ x=1 /\ y=12

---------------------------------------------------------------------    
(* Define the invariant from the annotation *)    
i == 
    /\ pc="l2" => x=1/\y=24
    /\ pc="l1" => x=1 /\ y=12
(* Define the safety property to check namely the partial correctness *)    

Init == init
Next == next










=============================================================================
\* Modification History
\* Last modified Fri Oct 02 09:35:17 CEST 2020 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
