-------------------------------- MODULE appex4_2 --------------------------------
EXTENDS TLC,Integers,Naturals
CONSTANTS x10,x20,min,max

ASSUME x10 \in Nat /\ x20 \in Nat /\ x20 # 0 (* requires *) 

(*

--fair algorithm division {
variables x1=x10,x2=x20,y1,y2,y3,z1,z2;
{
l1:assert x1=x10 /\ x2=x20 /\x10 \in Nat /\ x20 \in Nat /\ x20 # 0 
         /\ y1 = defaultInitValue /\ y2 = defaultInitValue  
         /\ y3 = defaultInitValue /\ z1 = defaultInitValue /\ z2 = defaultInitValue;
y1:=x1;y2:=0;y3:=x2;
l2:while (y3 \leq y1){
    y3:=2*y3;
    };
 l3:while (y3#x2){

    y2:=2*y2;
    y3:=y3 \div 2;
    l4:if (y3\leq y1) {
        y1:=y1-y3;
        y2:=y2+1;
        };
    };
   l5: z1:=y1;
    z2:=y2;
   l6:print <<x1,x2,z1,z2>>;
   l7: assert 0 \leq z1 /\ z1 < x2 /\ x1 = z2*x2+z1 /\ x1=x10 /\ x2=x20 /\x10 \in Nat /\ x20 \in Nat /\ x20 # 0 
    /\ y1\in Int /\ y2\in Int /\ y3\in Int /\ z1\in Int /\ z2 \in Int;
    }
 }

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x1, x2, y1, y2, y3, z1, z2, pc

vars == << x1, x2, y1, y2, y3, z1, z2, pc >>

Init == (* Global variables *)
        /\ x1 = x10
        /\ x2 = x20
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ z1 = defaultInitValue
        /\ z2 = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert( x1=x10 /\ x2=x20 /\x10 \in Nat /\ x20 \in Nat /\ x20 # 0
                /\ y1 = defaultInitValue /\ y2 = defaultInitValue
                /\ y3 = defaultInitValue /\ z1 = defaultInitValue /\ z2 = defaultInitValue, 
                "Failure of assertion at line 12, column 4.")
      /\ y1' = x1
      /\ y2' = 0
      /\ y3' = x2
      /\ pc' = "l2"
      /\ UNCHANGED << x1, x2, z1, z2 >>

l2 == /\ pc = "l2"
      /\ IF y3 \leq y1
            THEN /\ y3' = 2*y3
                 /\ pc' = "l2"
            ELSE /\ pc' = "l3"
                 /\ y3' = y3
      /\ UNCHANGED << x1, x2, y1, y2, z1, z2 >>

l3 == /\ pc = "l3"
      /\ IF y3#x2
            THEN /\ pc' = "ll6"
            ELSE /\ pc' = "l5"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z1, z2 >>

ll6 == /\ pc = "ll6"
       /\ PrintT(<<y1,y2,y3,x1,x2>>)
       /\ y2' = 2*y2
       /\ y3' = (y3 \div 2)
       /\ pc' = "l4"
       /\ UNCHANGED << x1, x2, y1, z1, z2 >>

l4 == /\ pc = "l4"
      /\ IF y3\leq y1
            THEN /\ y1' = y1-y3
                 /\ y2' = y2+1
            ELSE /\ TRUE
                 /\ UNCHANGED << y1, y2 >>
      /\ pc' = "l3"
      /\ UNCHANGED << x1, x2, y3, z1, z2 >>

l5 == /\ pc = "l5"
      /\ z1' = y1
      /\ z2' = y2
      /\ pc' = "l6"
      /\ UNCHANGED << x1, x2, y1, y2, y3 >>

l6 == /\ pc = "l6"
      /\ PrintT(<<x1,x2,z1,z2>>)
      /\ pc' = "l7"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z1, z2 >>

l7 == /\ pc = "l7"
      /\ Assert(          0 \leq z1 /\ z1 < x2 /\ x1 = z2*x2+z1 /\ x1=x10 /\ x2=x20 /\x10 \in Nat /\ x20 \in Nat /\ x20 # 0
                /\ y1\in Int /\ y2\in Int /\ y3\in Int /\ z1\in Int /\ z2 \in Int, 
                "Failure of assertion at line 31, column 8.")
      /\ pc' = "Done"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z1, z2 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2 \/ l3 \/ ll6 \/ l4 \/ l5 \/ l6 \/ l7
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


Qpc == pc="Done" => 
    /\ 0 \leq z1 /\ z1 < x2 /\ x1 = z2*x2+z1 /\ x1=x10 /\ x2=x20 /\x10 \in Nat /\ x20 \in Nat /\ x20 # 0
    

COND(U) ==    U # defaultInitValue => min \leq U /\ U \leq max
Qrte ==  COND(x1) /\ COND(x2) /\ COND(y1) /\ COND(y2) /\ COND(y3) /\ COND(z1) /\ COND(z2)

Iloop(u,v)  == x1=v*x2+u

i == Iloop(y1,y2)
=============================================================================
\* Modification History
\* Last modified Tue Oct 04 09:32:44 CEST 2022 by mery
\* Created Wed Nov 18 16:33:27 CET 2015 by mery
