-------------------------------- MODULE appex2_2 --------------------------------
(* Calcul de la fonction de MacCarthy *)
EXTENDS Naturals,TLC,Integers
------------------
CONSTANTS x,max,u
min == -max
--------------------------------
VARIABLES  y1,y2,z,pc
---------------------------------
BF(Y) == Y#u => Y \in min..max

ASSUME  BF(x) 

----------------------------

start == pc="START" /\ y1'=x /\ y2'=1/\ pc'="LOOP"  /\ UNCHANGED <<z>>

case1 == 
    /\ pc="LOOP" /\  y1  \leq 100 
    /\ y1'=y1+11 /\ y2'=y2+1 
    /\  UNCHANGED <<z,pc>> 

case2 == 
    /\ pc="LOOP" /\  y1  > 100 
    /\ pc'="OBS"
    /\  UNCHANGED <<z,y1,y2>>

case21 == 
    /\ pc="OBS"  /\ y2#1
    /\ y1'=y1-10 /\ y2'=y2-1
    /\ pc'="LOOP" 
    /\  UNCHANGED <<z>>

case22 ==
    /\ pc="OBS" /\ y2=1
    /\ z'=y1-10 /\ pc'="HALT"
    /\ UNCHANGED <<y1,y2>>
    --------------------
    
ePrint == pc="HALT" /\ PrintT(z)/\ UNCHANGED <<y1,y2,z,pc>>

-----------
Next == start  \/ case1 \/ case2 \/ case21 \/ case22 \/ UNCHANGED <<y1,y2,z,pc>> \/ ePrint
init1 == y1 \in Int /\ y2 \in Int /\ z \in Int /\ pc = "START"
Init  == y1 =u  /\ y2 = u  /\ z =u  /\ pc = "START"

--------------------------

Q1 == pc#"HALT"  (* c prned la valeur HALT *)
Qpartialcorrectness == pc="HALT" => z=IF x>100 THEN x-10 ELSE 91

Qy1 == BF(y1)
Qrte == BF(y1) /\ BF(y2) /\ BF(z)
Question == Qpartialcorrectness /\ Qrte

QQ == 0 \leq y2 /\ y2 \leq 2

test == QQ

=============================================


