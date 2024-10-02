-------------------------------- MODULE appex2_3 --------------------------------
EXTENDS Naturals,TLC,Integers
CONSTANTS x0,max,u
min == -max
VARIABLES  x,y,z,pc
D == min..max
rte(X) == X#u => X \in D
--------------
(* Précondition *) 
ASSUME x0 \in D /\  x0 \geq 2
-----------------------------
(* définitiobs *)

diviseurs(X) == {  m \in 1..X :  X % m = 0}
prime(X) ==  (diviseurs (X) = {1,X}) /\ X # 1
Locs == {"START","HALT","POINT"}
---------------------------------------------------
start == pc="START" /\ y'=2 /\ pc'="POINT"  /\ UNCHANGED <<x,z>> 

case1 == 
    /\ pc="POINT" /\  y \geq x
    /\ z'=TRUE
    /\ pc'="HALT"
    /\ PrintT(y)
    /\  UNCHANGED <<x,y>> 

case21 == 
    /\ pc="POINT"  /\ y<x /\ (x % y = 0)
    /\ pc'="HALT"
    /\ z'=FALSE
    /\  UNCHANGED <<x,y>>

case22 ==
    /\ pc="POINT"  /\ y<x /\ (x % y # 0)
    /\ y'=y+1
    /\  UNCHANGED <<x,z,pc>>

eprint == 
    /\ pc="HALT"
    /\ PrintT(z)
    /\ PrintT(x)
    /\ UNCHANGED <<x,y,z,pc>>
  
  --------  
Next == 
    \/ start  \/ case1 \/  case21 \/ case22 
    \/ UNCHANGED <<x,y,z,pc>> \/ eprint
    

Init  == x=x0 /\ y = u /\ z = u  /\  pc = "START"
-------------------------


Q1 == pc # "HALT"  (* pc prned la valeur HALT *)
Q2 == pc ="HALT" => (x=x0) /\ (z <=> (diviseurs(x)={1,x} /\ x#1))
Q3 == pc ="HALT" => (x=x0) /\ (z = prime(x))
Q4 == pc \in Locs
Q5 ==  rte(x) /\ rte(y)

Q == Q1 /\  Q2 /\ Q3 /\ Q4 /\ Q5


=============================================


