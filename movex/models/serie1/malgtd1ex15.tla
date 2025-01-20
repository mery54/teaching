
-------------------------------- MODULE malgtd1ex15 -------------------------------
EXTENDS  TLC,Integers,Naturals,Sequences
CONSTANTS  amin,amax,U,n0 

i0 == U
v0 ==  [p \in 0..n0-1 |-> p ]
division(a,b) == a \div b

ssum ==  [p \in 0..n0-1 |-> division(p*(p+1),2)]
s0 == U
D == amin..amax
DOM(x) == x=U \/ x \in D
L == {"l1","l0","l2","l3","l4","l5","l6"}


S == LET seq == v0
    Sum[ k \in 0..n0-1] == IF k = 0 THEN seq[k] ELSE seq[k] + Sum[k-1]
    IN  Sum[n0-1]  

SUM(m) == LET seq == v0
    Sum[ k \in 0..n0-1] == IF k = 0 THEN seq[k] ELSE seq[k] + Sum[k-1]
    IN  Sum[m]  

pre(a,b,c,d) == 
    /\ a \in Nat /\ a # 0 
    /\ b \in  [0..n0-1 -> Int] 
    /\ c \in Int   
    /\ d \in Int
------
    
VARIABLES  n,v,s,i,pc
----------------    
ASSUME pre(n0,v0,s0,i0)
----------------------------------------------------------
al0l1 ==
    /\ pc="l0" 
    /\ pc'="l1"
    /\ s'=v[0]
    /\ UNCHANGED <<n,i,v>>
    
al1l2 ==
    /\ pc="l1" 
    /\ pc'="l2"
    /\ i'=1
    /\ UNCHANGED <<n,v,s>>
    
    al2l3 ==
    /\ pc="l2" 
    /\ pc'="l3"
    /\ i< n 
    /\ UNCHANGED <<n,v,s,i>>
      al2l6 ==
    /\ pc="l2" 
    /\ pc'="l6"
    /\ i \geq  n 
    /\ UNCHANGED <<n,v,s,i>>
    
    al3l4 ==
    /\ pc="l3" 
    /\ pc'="l4"
    /\ s'=s+v[i]
    /\ UNCHANGED <<n,v,i>>
    
    al4l5 ==
    /\ pc="l4" 
    /\ pc'="l5"
    /\ i'=i+1
    /\ UNCHANGED <<n,v,s>>
    
    al5l3 ==
    /\ pc="l5" 
    /\ pc'="l3"
    /\ i< n 
    /\ UNCHANGED <<n,v,s,i>>
      
      al5l6 ==
    /\ pc="l5" 
    /\ pc'="l6"
    /\ i \geq  n 
    /\ UNCHANGED <<n,v,s,i>>
    
skip == UNCHANGED <<n,v,s,i,pc>>
----------------------------------------------------------
inv ==
    /\ n \in Int
    /\ i \in Int
    /\ s \in Int
    /\ v \in [0..n-1 -> amin..amax]
    /\ pc="l1" => pre(n0,v0,s0,i0) /\ s=ssum[0] /\ i = i0 /\ n=n0 /\ v=v0
    /\ pc="l2" => pre(n0,v0,s0,i0) /\ s=ssum[0] /\ i = 1 /\ n=n0 /\ v=v0
    /\ pc="l3" => pre(n0,v0,s0,i0) /\ s=ssum[i-1] /\ i \in 1..n-1 /\ n=n0 /\ v=v0 
    /\ pc="l4" => pre(n0,v0,s0,i0) /\ s=ssum[i] /\ i \in 1..n-1 /\ n=n0 /\ v=v0 
    /\ pc="l5" => pre(n0,v0,s0,i0) /\ s=ssum[i-1] /\ i \in 2..n /\ n=n0 /\ v=v0 
    /\ pc="l6" => pre(n0,v0,s0,i0) /\ s=ssum[i-1] /\ i=n /\ n=n0 /\ v=v0 
      
   
rte ==   DOM(s) /\ DOM(i) /\ DOM(n) /\ (pc \in L)  
  
-----------------------------
Init == pc="l0" /\ i=i0 /\ s = s0 /\ v=v0 /\ n=n0
Next == al0l1 \/ al1l2 \/ al2l3 \/ al2l6 \/ al3l4 \/ al4l5 \/ al5l3 \/ al5l6
----------------------------------------------------------

-----------------------------
test == inv /\ rte
=============================================
