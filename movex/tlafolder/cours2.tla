-------------------------------- MODULE cours2 ------------------------------
EXTENDS Naturals,TLC 
----------------------------------------------------------------------------
CONSTANTS
		\* @type: Int;
		max
----------------------------------------------------------------------------
VARIABLES
	\* @type: Int;
	np
-----------------------------------------------------------------------------
(* Assumptions *)
ASSUME max < 50000

-------------------------
(*  tentative 1 *)
entrer == np < max /\ np'=np +1
sortir ==  np > 0 /\ np'=np-1
Next == 
     \/ entrer 
     \/ sortir
Init == np=0
test1 == np # 12
test == 0 <= np /\ np <= max
-----------------------------------------------------------------------------
(* tentative 2 *)
entrer2 == np<max /\ np'=np+1 
next2 ==  entrer2  \/  sortir
-----------------------------------------------------------------------------
(* tentative 3 *)
sortir2 == np>0 /\ np'=np-1 
next3 ==  entrer2  \/  sortir2
------------------
safety1 == np \leq max
safety2 == 0 \leq np
question1 ==  np # 6
Inv ==  0 \leq np /\ np \leq max
ConstInit ==
  /\ max \in 19..200
  

=============================================================================
sh  apalache/bin/apalache-mc  check  --inv=Inv   --length=20 --cinit=ConstInit cours2.tla
