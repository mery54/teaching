-------------------------------- MODULE appex1_1 --------------------------------
(* modules de base importables *)
EXTENDS Naturals, Integers, TLC 
----------------------------------------------------------------------------
CONSTANTS max
----------------------------------------------------------------------------
VARIABLES  np
-------------------------------------
(*  tentative 1 *)
entrer == 
    /\ TRUE
    /\ np'=np +1
sortir == np'=np-1
next1 == entrer \/ sortir
Init == np=0
-----------------------------------------------------------------------------
(* tentative 2 *)
entrer2 == np<max /\ np'=np+1 
next2 ==  entrer2  \/  sortir
-----------------------------------------------------------------------------
(* tentative 3 *)
sortir2 == np>0 /\ np'=np-1 
next3 ==  entrer2  \/  sortir2
------------------
Safety1 == np \in Int
Safety2 == np \leq max 
Safety3 == np \geq 0
qq ==  np # 89

Safety ==  Safety1 /\ Safety2 /\ Safety3
Check ==  rte
Test == Safety

=============================================================================
