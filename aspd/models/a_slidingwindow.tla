----------------- MODULE a_slidingwindow -----------------
EXTENDS Integers,TLC
CONSTANTS
	\* @type: Int;
	l,
	\* @type: Int;
	n,
	\* @type: Int;
	NIL
------------------------------------------------------------
ASSUME l \geq 0
------------------------------------------------------------   
VARIABLES
	\* @type: Int;	
	i,
	\* @type: Int -> Int;
	INPUT,
	\* @type: Int -> Int;	
	OUTPUT,
	\* @type: Set(Int);	
	got,
	\* @type: Set(Int);		
	ack,
	\* @type: Bool;		
	complete,
	\* @type: Int -> Int;
	chan
--------------------------------------------------
(* actions *)
send == 
    /\ PrintT("send")
    /\ PrintT(INPUT)
    /\ PrintT(chan)
    /\ i \leq n
    /\  \E v \in 0..n: i \leq v /\ v \leq i+l /\ v \notin got 
	/\ LET k == CHOOSE val \in 0..n :( val \in i..i+l /\ val \notin  got)
         IN  
             /\ chan'=[chan EXCEPT![k] = INPUT[k] ]
 	/\ UNCHANGED <<i,INPUT,OUTPUT,got,ack,complete>>
receive ==  
    /\ PrintT("receive")
     /\ \E  j \in 0..n: j \in  i..i+l \cap 0..n /\  chan[j] # NIL 
     /\ LET k == CHOOSE val \in i..i+l :(chan[val]#NIL)
          IN  
             /\ ack'= ack \cup  { k}
             /\ OUTPUT'=[OUTPUT  EXCEPT![k]= chan[k]]
 	/\ UNCHANGED <<i,INPUT,got,complete,chan>>

receiveack(k) ==
    /\ PrintT("receiveack")
    /\ k \in  ack             
    /\ ack'= ack \ { k}
    /\ got'=got \cup {k}
 	/\ UNCHANGED <<i,INPUT,OUTPUT,complete,chan>>

completed ==  
	/\ PrintT("completed") /\ complete # TRUE /\ i=n+1 /\ got={} /\  complete'=TRUE
 	/\ UNCHANGED <<i,INPUT,OUTPUT,got,ack,chan>>


sliding ==
    /\ PrintT("slide")
    /\ PrintT(i)
    /\ got # {}
	/\  i \in   got
	/\  i+l <  n
	/\  i' = i+1 
	/\  got'=  got \ { i}
	/\  ack'= ack\{ i}
 	/\ UNCHANGED <<INPUT,OUTPUT,complete,chan>>



completesliding ==
    /\ got # {}
	/\  i \in   got
	/\  i+l \geq   n
	/\ i \leq n
	/\ i'=i+1
	/\  got'=  got \ { i}
	/\  ack'= ack\{ i}
 	/\ UNCHANGED <<INPUT,OUTPUT,complete,chan>>




loosingchan ==
    /\ PrintT("loosingchan")
	/\ \E j \in  0..n : j \in i..i+l /\  chan[j]#NIL /\  j \notin  got
        /\ LET k == CHOOSE val \in  0..n : (val \in i..i+l /\ val \notin  got)
              IN  
                 /\ chan'=[chan EXCEPT![k] = NIL ]

    /\ UNCHANGED <<i,INPUT,OUTPUT,got,ack,complete>>


loosingack ==
   /\ PrintT("loosingack")
    /\ \E j \in  0..n: j \in ack
    /\ LET k == CHOOSE val \in 0..n :(val \in  ack)
         IN  
             /\ ack'=ack \{k}
    /\ UNCHANGED <<i,INPUT,OUTPUT,got,complete,chan>>

skip == UNCHANGED <<i,INPUT,OUTPUT,got,ack,complete,chan>>
--------------------------------------------------	

NextNoLoss ==
	   \/ send \/ receive
	   \/ (\E k \in 0..n : receiveack(k))
	   \/ completed \/ sliding \/ completesliding  \/ skip
NextLoss ==  loosingchan \/ loosingack 
Next == NextNoLoss (*  \/ NextLoss \/ UNCHANGED <<i,INPUT,OUTPUT,got,ack,complete,chan>> *)

Init ==
	/\ i=0
	/\ INPUT=[j \in 0..n |-> 3*j]
	/\ OUTPUT=[j \in 0..n |-> NIL]
	/\ got={} /\ ack={} /\ complete=FALSE 
	/\ chan=[j \in 0..n |-> NIL]
----------------------------------------------------------------------	
inv0  ==
    /\ (ack \cup got) \subseteq (i..i+l \cap 0..n)
    /\ \A k  \in 0..i-1 : OUTPUT[k] = INPUT[k]
inv1 == (ack \cup got) \subseteq (i..i+l \cap 0..n)
inv2 == \A k  \in 0..i-1 : OUTPUT[k] = INPUT[k]
--------------------------------------------------
\* 
Q1 == 	OUTPUT#[j \in 0..n |-> 3*j]
Q2 == i # n+1 \/ got#{} \/ ack#{}
Q3 == i #n
Q4 == ack \cap got = {}	 (* Propriété non valide *)

--------------------------------------------------
CInit == l=3 /\ n=5 /\ NIL=-1
==================================================
