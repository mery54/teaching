------------------- MODULE malgtd1ex1 -----------------
EXTENDS Integers,Naturals
----------------------------------------
CONSTANTS x0,y0
---------------------------------------
VARIABLES  x,y
-----------------------------------
f[u \in Nat ,v \in Nat]== IF u < v THEN f[u,v-u] ELSE IF u > v THEN f[u-v,v]  ELSE u

ASSUME x0 \in Nat /\ y0 \in Nat
Init == x=x0 /\ y=y0
-----------------------------------
(* actions *)
a1 == 
    /\ x > y 
    /\ x'=x-y
    /\ y'=y
a2 == x < y /\ y'=y-x /\ x'=x
over == x=y /\ x'=x /\ y'=y
------------------------------------
Next == a1 \/ a2  \/ over 

------------------------------------
(* Propriétés de sûreté à vérifier *)
test == x # y  \* ko
prop1 == x \geq 0 \* ok


TypeOK ==
       /\ x \in Int
       /\ y \in Int
Inv  ==
     /\  0 <= x /\ x <= x0
     /\  0 <= y /\ y  <=y0
     /\ f[x,y] = f[x0,y0]
P1 == [] Inv
P2 == [] (0 <= y /\ y <= y0) 

=============================================



