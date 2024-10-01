-------------------------------- MODULE appex1_4 --------------------------------
(* modules de base importables *)
EXTENDS Naturals, Integers, TLC 
----------------------------------------------------------------------------
CONSTANTS  x1,x2,U,MAX

MIN == -MAX
----------------------------------------------------------------------------
VARIABLES  y1,y2,y3,z1,z2,pc
-----------------------------------------------------------------------------
locs == {"START","HALT","LOOP"}
-----------------------------------------------------------------------------
BF(X) == X#U => X \in MIN..MAX

ASSUME  BF(x1) /\ BF(x2)
-----------------------------------------------------------------------------


Init == pc="START" /\ y1=U /\ y2 = U /\ y3=U /\ z1 = U /\ z2 = U
-----------------------------------------------------------------------------
actionSTART_LOOP ==
	      /\ pc = "START"
	      /\ pc'="LOOP"
	      /\ y1'=0
	      /\ y2'=0
	      /\ y3'=x1
	      /\ UNCHANGED <<z1,z2>>


actionLOOP_HALT ==
	     /\ pc="LOOP"
	     /\ y3=0
	     /\ pc'="HALT"
	      /\ y1'=y1
	      /\ y2'=y2
	      /\ y3'=y3
	      /\ z1'=y1
	      /\ z2'=y2



actionLOOP_LOOP ==
	     /\ pc="LOOP"
	     /\ y3#0
	     /\ pc'=pc
	     /\ y1'= IF y2+1=x2 THEN y1+1 ELSE y1
	     /\ y2'= IF y2+1 = x2 THEN 0 ELSE y2+1
	     /\ y3'=y3-1
	     /\ z1'=z1
	     /\ z2'=z2


skip == UNCHANGED << y1,y2,y3,z1,z2,pc>>

-----------------------------------------------------------------------------


Next == 
    \/ actionSTART_LOOP 
    \/  actionLOOP_HALT 
    \/ actionLOOP_LOOP 
    \/ skip


-----------------------------------------------------------------------------

(* vérification du contrôle *)
safety1 == pc \in locs
(* correction partielle *)

safety2 == pc="HALT" => z1 = x1 \div x2 /\ z2= x1 % x2 /\ PrintT(z1) /\ PrintT(z2)

safety3 == pc="HALT" =>     x1 = z1*x2 +z2  /\ 0 \leq z2 /\ z2 < x2


safety4 == BF(z1) /\BF(z2) /\BF(y1) /\BF(y2) /\BF(y3)


tes == safety1 /\ safety2 /\ safety3 /\ safety4
 
Safety == safety1 /\ safety2  /\ safety3  /\ safety4 
=============================================================================
