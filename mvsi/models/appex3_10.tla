------------------------------- MODULE appex3_10 -------------------------------
(* computing the maximum value of an array f *)

EXTENDS Naturals, TLC,Integers
CONSTANTS undef,n0,f0,i0,m0,min,max
VARIABLES n,f,m,i,pc
--------------------------------
def0 == [j \in 0..n0-1 |-> n0-j]

--------------------------------
(* precondition *)

ASSUME n0 \in Nat /\ n0 # 0  /\ f0 = def0 /\ i0 \in Int

Init == /\ i = i0
        /\ m = m0
        /\ f=f0
        /\ n=n0
        /\ pc = "l0"
----------------------------------        
l0l1 == /\ pc = "l0" 
        /\ m' = f[0]
        /\ pc'= "l1"
        /\ UNCHANGED <<n,f,i>>
   
        
l1l2 == /\ pc = "l1"
        /\ i' = 1
        /\ pc'= "l2"  
        /\ UNCHANGED <<n,f,m>>
            
             
l2l3 == /\ pc = "l2"
        /\ i < n
        /\ pc'= "l3"
        /\ UNCHANGED <<n,f,m,i>>
   
           
l2l8 == /\ pc = "l2"
        /\ (i \geq n)
        /\ m' = m
        /\ i' = i
        /\ pc'= "l8"
        /\ UNCHANGED <<n,f>>
          
l3l4 == /\ pc = "l3"
        /\ f[i] > m
        /\ m' = m
        /\ i' = i
        /\ pc'= "l4"
        /\ UNCHANGED <<n,f>>
           
        
l3l6 == /\ pc = "l3"
        /\ (f[i] \leq m)
        /\ m' = m
        /\ i' = i
        /\ pc'= "l6"
        /\ UNCHANGED <<n,f>>
   
l4l5 == /\ pc = "l4"
        /\ m' = f[i]
        /\ i' = i
        /\ pc'= "l5"
        /\ UNCHANGED <<n,f>>
   
          
l5l6 == /\ pc = "l5"
        /\ m' = m
        /\ i' = i
        /\ pc'= "l6"
        /\ UNCHANGED <<n,f>>
           
l6l7 == /\ pc = "l6"
        /\ m' = m
        /\ i' = i + 1
        /\ pc'= "l7"
       /\ UNCHANGED <<n,f>>
           
        
l7l3 == /\ pc = "l7"
        /\ i < n 
        /\ m' = m
        /\ i' = i
        /\ pc= "l3"
        /\ UNCHANGED <<n,f>>
    
 l7l8 == 
        /\ pc = "l7"
        /\ i \geq n 
        /\ m' = m
        /\ i' = i
        /\ pc'= "l8"
        /\ UNCHANGED <<n,f>>
   
 
 
Next == \/ l0l1
        \/ l1l2
        \/ l2l3
        \/ l2l8
        \/ l3l4
        \/ l3l6
        \/ l4l5
        \/ l5l6
        \/ l6l7
        \/ l7l3
        \/ l7l8
        \/ UNCHANGED <<n,m,i,f,pc>>
 
pre0 == n0 \in Nat /\ n0 # 0  /\ f0 = def0 /\ i0 \in Int
pre1 == f=f0 /\ n=n0 /\ pre0

   zinf == min..max
  ninf == 0..max
  
  
  Dl0l1 ==  0\leq 0 /\ 0 \leq n0-1
  Dl1l2 == 1 \in zinf
 inv ==
   /\ pc \in {"l0","l1","l2","l3","l4","l5","l6","l7","l8"}
   /\ n \in Int /\ f = def0 /\ i \in Int /\ m \in Int 
   /\ pc="l0" =>   f=f0 /\ n=n0 /\ m=m0 /\ i = i0/\ pre0 /\ Dl0l1
   /\ pc="l1" =>  f=f0 /\ n=n0 /\ m=f[0] /\ i = i0 /\ pre0 /\ Dl1l2
   /\ pc ="l2" =>f=f0 /\ n=n0 /\ m=f[0] /\ i = 1 /\ pre0
   /\ pc="l3" =>  (\E j \in 0..i-1 : f[j]=m) /\ (\A k \in 0..i-1: f[k] \leq m) /\ (i < n) /\  pre1
   /\ pc="l4" =>  (\E j \in 0..i-1 : f[j]=m) /\ (\A k \in 0..i-1: f[k] \leq m) /\ (i < n) /\ (f[i]>m) /\pre1
   /\ pc="l5"  =>  (\E j \in 0..i-1 : f[j]=m) /\ (\A k \in 0..i: f[k] \leq m) /\ (i < n) /\ (f[i]>m) /\pre1
   /\ pc="l6" =>   (\E j \in 0..i : f[j]=m) /\ (\A k \in 0..i: f[k] \leq m)  /\pre1
   /\ pc="l7" =>   (\E j \in 0..i-1 : f[j]=m) /\ (\A k \in 0..i-1: f[k] \leq m) /\ (i \leq n)  /\pre1
   /\ pc="l8" =>   (\E j \in 0..i-1 : f[j]=m) /\ (\A k \in 0..i: f[k] \leq m)  /\pre1 /\ i=n
   
 
  
runtimeerrors ==  m \in zinf /\ i \in zinf /\ n \in zinf


=============================================================================

