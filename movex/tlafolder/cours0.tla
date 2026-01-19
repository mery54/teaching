------------------- MODULE cours0 -----------------
EXTENDS Integers, Naturals,TLC
CONSTANTS x0,y0
VARIABLES  x,y
-----------------------------------
ASSUME x0 \in Nat /\ y0 \in Nat 
Init == x=x0 /\ y=y0 
-----------------------------------
(* actions *)
finger == 
    /\ y # 0 
    /\ x'=x+1
    /\ y'=y-1
over == y=0 /\ x'=x /\ y'=y
------------------------------------
Next == finger \/ over 
------------------------------------
(* Safety properties to be verified *)
TypeOK ==
       /\ x \in Int
       /\ y \in Int
Inv  ==
     /\ x \geq x0 /\ x <= x0+y0
     /\  0 <= y /\ y  <=y0
     /\ x+y = x0+y0
P1 == [] Inv
P2 == [] (0 <= y /\ y <= y0) 
Q1 == y # 0

=============================================



