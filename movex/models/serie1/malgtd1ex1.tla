------------------- MODULE malgtd1ex1 -----------------
EXTENDS Naturals
----------------------------------------
CONSTANTS a,b
---------------------------------------
VARIABLES  x,y
-----------------------------------
ASSUME a \in Nat /\ b \in Nat
toto == x=a /\ y=b
-----------------------------------
(* actions *)
a1 == 
    /\ x > y 
    /\ x'=x-y
    /\ y'=y
a2 == x < y /\ y'=y-x /\ x'=x
over == x=y /\ x'=x /\ y'=y
------------------------------------
go == a1 \/ a2  \/ over 

------------------------------------
(* Propriétés de sûreté à vérifier *)
test == x # y 
prop1 == x \geq 0 \* ok
prop2 == x+y \leq a+b \* ok
tocheck == prop1 /\ prop2
=============================================



