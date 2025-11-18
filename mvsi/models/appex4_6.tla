
---------------------- MODULE appex4_6 --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT MAXINT,x10,x20,y10,y20,y30,z0,MININT 


pre == x10 \in Nat /\ x20 \in Nat 

post(Y10,Y20,Y30,X10,X20,Z0,Y1,Y2,Y3,X1,X2,Z) == Z = X10^X20
(*
-termination

--fair algorithm Power {
  variables 
            y1;
            y2;
            y3;
            x1=x10;
            x2=x20;
            z;

{
    l0: 
    y1:=x1;
    y2:=x2;
    y3:=1;
   l1:while (y2 # 0) {
      l2:if ( y2 % 2 # 0) {
        l3:y2:=y2-1;
        l4:y3:=y3*y1;
        l5:skip ;
      };
     l6: y1 := y1*y1;
     l7:y2:= y2 \div   2;
     l8:skip;
    };
    l9: z := y3;
    l10:skip;
 
}

}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES y1, y2, y3, x1, x2, z, pc

vars == << y1, y2, y3, x1, x2, z, pc >>

Init == (* Global variables *)
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ x1 = x10
        /\ x2 = x20
        /\ z = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ y1' = x1
      /\ y2' = x2
      /\ y3' = 1
      /\ pc' = "l1"
      /\ UNCHANGED << x1, x2, z >>

l1 == /\ pc = "l1"
      /\ IF y2 # 0
            THEN /\ pc' = "l2"
            ELSE /\ pc' = "l9"
      /\ UNCHANGED << y1, y2, y3, x1, x2, z >>

l2 == /\ pc = "l2"
      /\ IF y2 % 2 # 0
            THEN /\ pc' = "l3"
            ELSE /\ pc' = "l6"
      /\ UNCHANGED << y1, y2, y3, x1, x2, z >>

l3 == /\ pc = "l3"
      /\ y2' = y2-1
      /\ pc' = "l4"
      /\ UNCHANGED << y1, y3, x1, x2, z >>

l4 == /\ pc = "l4"
      /\ y3' = y3*y1
      /\ pc' = "l5"
      /\ UNCHANGED << y1, y2, x1, x2, z >>

l5 == /\ pc = "l5"
      /\ TRUE
      /\ pc' = "l6"
      /\ UNCHANGED << y1, y2, y3, x1, x2, z >>

l6 == /\ pc = "l6"
      /\ y1' = y1*y1
      /\ pc' = "l7"
      /\ UNCHANGED << y2, y3, x1, x2, z >>

l7 == /\ pc = "l7"
      /\ y2' = (y2 \div   2)
      /\ pc' = "l8"
      /\ UNCHANGED << y1, y3, x1, x2, z >>

l8 == /\ pc = "l8"
      /\ TRUE
      /\ pc' = "l1"
      /\ UNCHANGED << y1, y2, y3, x1, x2, z >>

l9 == /\ pc = "l9"
      /\ z' = y3
      /\ pc' = "l10"
      /\ UNCHANGED << y1, y2, y3, x1, x2 >>

l10 == /\ pc = "l10"
       /\ TRUE
       /\ pc' = "Done"
       /\ UNCHANGED << y1, y2, y3, x1, x2, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9 \/ l10
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

L == {"l0","l1","l2","l3","l4","l5","l6","l7","l8","l9","l10","Done"}
D == MININT..MAXINT

DD(X) == X#defaultInitValue => X \in D

i == 
    /\ pc \in L
    /\ DD(y1) /\ DD(y2) /\ DD(y3) /\ DD(z)
    /\ pc="l1" => y1=x1 /\ y2=x2 /\ y3=1
Q1 == pc # "Done"
Qpc == pc ="Done" => z=x1^x2
I == 
    /\ y1#defaultInitValue => y1 \in D  
    /\ y2#defaultInitValue => y2 \in D 
    /\ y3#defaultInitValue =>  y3 \in D 
    /\ z#defaultInitValue =>  z \in D
    /\ pc \in L
    /\ pc="l1" => y3*(y1^y2) = x1^x2
    /\ pc="l2" => y3*(y1^y2) = x1^x2
    /\ pc="l3" => y3*(y1^y2) = x1^x2
    /\ pc="l4" => y3*y1*(y1^y2) = x1^x2
    
Inv ==
    /\ pc = "l0" =>  pre /\ x1=x10 /\ x2 = x20 
    /\ pc = "l1" =>  pre /\ y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\ pc = "l2" =>   y2 # 0 /\ pre /\ y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\ pc = "l3" => (y2 % 2 # 0) /\ y2 # 0 /\ pre /\ y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\ pc = "l4" =>   pre /\ y3*y1*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\ pc =" l5" => (y2 % 2 = 0) /\ y2 # 0 /\ pre /\ y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\  pc="l6" =>  (y2 % 2 = 0)  /\ pre /\ y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20
    /\  pc="l7" =>  (y2 % 2 = 0)  /\ pre /\ y3*y1^(y2 \div  2)=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\  pc="l8" =>  pre /\ y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\ pc="l9" =>  pre /\ y2=0 /\  y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 
    /\  pc="l10" =>  pre /\ y2=0 /\  y3*y1^y2=x1^x2 /\ x1=x10 /\ x2 = x20 /\ z = y3


test == Qpc
==================================================================
\* Modification History
\* Last modified Wed Nov 29 17:41:38 CET 2023 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
