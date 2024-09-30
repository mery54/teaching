------------------- MODULE appex1_2 -----------------
EXTENDS Naturals,TLC
CONSTANTS a,b
VARIABLES  x,y
-----------------------------------
ASSUME a \in Nat /\ b \in Nat
Init == x=a /\ y=b
-----------------------------------
a1 == 
    /\ x > y 
    /\ x'=x-y 
    /\ y'=y
a2 == 
    /\ x < y 
    /\ y'=y-x 
    /\ x'=x
over == x=y /\ x'=x /\ y'=y
------------------------------------
Next == 
    \/ a1 
    \/ a2  
    \/ over 
------------------------------------
(* Propriétés de sûreté à vérifier *)
question == x # y 
prop1 == x \geq 0 /\ y \geq 0
prop2 == x+y \leq a+b
prop == question
Check == prop2
=============================================



