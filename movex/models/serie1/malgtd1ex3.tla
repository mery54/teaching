------------------- MODULE malgtd1ex3  -----------------
EXTENDS Integers,TLC,Naturals
CONSTANTS UND,x10,x20,maxi,mini
VARIABLES x1,x2,y1,y2,y3,z1,z2,pc
----------------------------------
ASSUME x10 \in Nat /\ x20 \in Nat /\ x20 # 0
labels == {"START","LOOP","HALT"}

Init == 
    /\ pc="START" 
    /\ x1 = x10 /\ x2 = x20
    /\ y1=UND /\ y2=UND /\ y3 = UND 
    /\ z1=UND /\ z2 =UND

(*  y1 \in min..max  /\ y2 \in min..max /\ y3 \in min..max /\ z1 \in min..max /\ z2 \in min..max *)

start_loop == 
    /\ pc = "START"
    /\ pc' = "LOOP"
    /\ y1'=0 /\ y2'=0 /\ y3'=x1
    /\ UNCHANGED <<z1,z2,x1,x2>>
     
loop_loop == 
    /\ pc = "LOOP" /\ y3 # 0
    /\ y1' = IF y2+1=x2  THEN y1+1 ELSE y1 
    /\ y2' = IF y2+1=x2  THEN 0 ELSE y2+1
    /\ y3' = y3 -1 
    /\ UNCHANGED <<pc,x1,x2,z1,z2>>
    
 loop_halt == 
    /\ pc = "LOOP" /\ pc'="HALT" /\ y3 = 0
    /\ z1' = y1 /\ z2'=y2
    /\ UNCHANGED <<x1,x2,y1,y2,y3>>
    
 Over == 
    /\ pc="HALT"  /\ PrintT(z1) /\  PrintT(z2) 
    /\ UNCHANGED<<pc,x1,x2,y1,y2,y3,z1,z2>>
    
  next == start_loop \/ loop_loop  \/ loop_halt\/ Over
  
  ------------------------
  safety1 == pc="HALT" => 0 \leq z2  /\ z2  < x2 /\ x1=z1*x2+z2 /\ x1=x10 /\ x2=x20
  
  D == mini..maxi
  
  DD(X) ==  (X # UND => X \in D)
  
  safety2 == DD(y1) /\ DD(y2) /\ DD(y3)  /\ DD(z1) /\ DD(z2)
  
  
  test == safety1
=============================================



