--------- MODULE appex3_12 --------
EXTENDS Integers,TLC
CONSTANTS x0,z0,y10,y20,y30  (* x0 is the input *)
--------------------------------------------------------------
VARIABLES
    pc,x,y1,y2,y3,z

vars == <<pc,x,y1,y2,y3,z>>
--------------------------------------------------------------
al0l1 == pc="l0" /\ y1'=0 /\y2'=1 /\ y3'=1 /\ pc'="l1" /\ z'=z /\ x'=x
al1l2 == pc="l1" /\ y2 \leq x /\pc'="l2" /\  UNCHANGED <<y1,y2,y3,z,x>>
al1l4 == pc="l1" /\ y2 >  x /\ pc'="l4" /\ UNCHANGED <<y1,y2,y3,z,x>>
al2l3 == pc="l2" /\ y1'=y1+1 /\y2'=y2+y3+2 /\ y3'=y3+2 /\ pc'="l3" /\ z'=z /\ x'=x
al3l2 == pc="l3" /\ y2 \leq x /\pc'="l2" /\  UNCHANGED <<y1,y2,y3,z,x>>
al3l4 == pc="l3" /\ y2 >  x /\ pc'="l4" /\ UNCHANGED <<y1,y2,y3,z,x>>
al4l5 == pc="l4" /\ z'=y1 /\pc'="l5" /\  UNCHANGED <<y1,y2,y3,x>>
--------------------------------------------------------------
Init == x=x0 /\ y1=y10 /\ y2 = y20 /\ y3 = y30/\ z=z0 /\ pc="l0"
Next == al0l1 \/ al1l2 \/ al1l4\/ al2l3 \/ al3l2 \/ al3l4 \/ al4l5   \/ UNCHANGED vars
-----------
MAX == 32768  (* 16 bits *)
D == 0..MAX
(*  x \leq 32768 *)
DD(X) ==  X \in D


Safety_absence ==  DD(x) /\ DD(y1)  /\ DD(y2) /\ DD(y3) /\ DD(z)

Safety_partialcorrectness == pc="l5" =>  z*z\leq x /\ x < (z+1)*(z+1)

TYPE0 == x0 \in Nat  /\ y10 \in D /\  y20 \in D /\ y30 \in D /\  z0 \in D 
Inv == 
  	/\ pc="l0" => x=x0 /\ y1=y10 /\ y2 = y20 /\ y3 = y30 /\ z = z0  /\ TYPE0
	/\ pc="l1" => x=x0 /\ y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  y1*y1\leq x /\ TYPE0
	/\ pc="l2" => x=x0 /\ y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  y1*y1\leq x /\ y2 \leq x   /\ TYPE0
	/\ pc="l3" => x=x0 /\ y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  y1*y1\leq x /\ TYPE0
	/\ pc="l4" => x=x0 /\ y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  y1*y1\leq x /\ x < y2 /\ TYPE0
	/\ pc="l5" => x=x0 /\ y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  z*z\leq x /\ x < (z+1)*(z+1) /\ TYPE0 


check ==  
  /\ Inv
  /\ Safety_partialcorrectness
  /\ Safety_absence

=========
