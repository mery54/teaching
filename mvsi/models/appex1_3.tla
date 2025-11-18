-------------------------------- MODULE appex1_3 --------------------------------
(* petri10 *)
EXTENDS Naturals,TLC
CONSTANTS Places,N,Q,B
VARIABLES  M

-----------------------------

t1 == 
	/\ M["p2"]  \geq 1  /\  M["pi"]  \geq 1
	/\ M'=  [[[M EXCEPT!["p1"]= 1] 
	             EXCEPT!["pi"]= @-1] 
	             EXCEPT!["p2"]=@-1]

t2 == 
	/\ M["p1"] \geq 1 /\ M["p5"] <  B
	/\ M'=  [[[M EXCEPT!["p1"]=@-1] 
	             EXCEPT!["p5"]=M["p5"]+1] 
	             EXCEPT!["p2"]=1]

t3 == 
	/\ M["p5"] \geq 1 /\ M["p4"] \geq 1
	/\ M'=  [[[M EXCEPT!["p3"]=@+1] 
	             EXCEPT!["p5"]=@-1] 
	             EXCEPT!["p4"]=@-1]



t4 == 
	/\ M["p3"] \geq 1 /\ M["po"]<Q 
	/\ M'=  [[[M EXCEPT!["p3"]= M["p3"]-1] 
                 EXCEPT!["po"]=M["po"]+1] 
                 EXCEPT!["p4"]=M["p4"]+1]

-----------------------------

Init1 ==  M = [p \in Places |-> IF p \in {"p4","p2"} THEN 1 ELSE 
                IF p = "pi" THEN N ELSE 0 ]
Init == Init1
Next == t1 \/ t2 \/ t3 \/ t4 \/ M'=M


-----------------------------

TypeInvariant ==  \A p \in Places :  M[p] \geq 0

Inv1 ==  M["pi"]+M["p5"]+M["po"]+M["p1"]+ M["p3"]  = N 

Inv2 ==  M["po"] \leq  Q

QInv4 ==  M["pi"]+M["p5"]+M["po"]+M["p2"]+M["p4"] = N+2 
Inv5 ==  M["p3"]+M["p4"]+M["p1"]+M["p2"] = 2

Inv3 ==  M["p3"] = 0

Inv6 == M["p1"] + M["p2"] = 1
 
Question == M["po"] #  N
Safety1 ==  M["p2"] \leq  1  /\ M["p2"] \geq  0
Check == Inv6
safe == Inv3
=============================================
