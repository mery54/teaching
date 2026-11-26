-------------------------------- MODULE pluscal_division --------------------------------
EXTENDS TLC,Integers,Naturals
CONSTANTS x1,x2,min,max

(*

-- algorithm division {
variables y1,y2,y3,z1,z2;
{
l1:y1:=x1;y2:=0;y3:=x2;
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
    }
 }

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES y1, y2, y3, z1, z2, pc

vars == << y1, y2, y3, z1, z2, pc >>

Init == (* Global variables *)
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ z1 = defaultInitValue
        /\ z2 = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ y1' = x1
      /\ y2' = 0
      /\ y3' = x2
      /\ pc' = "l2"
      /\ UNCHANGED << z1, z2 >>

l2 == /\ pc = "l2"
      /\ IF y3 \leq y1
            THEN /\ y3' = 2*y3
                 /\ pc' = "l2"
            ELSE /\ pc' = "l3"
                 /\ y3' = y3
      /\ UNCHANGED << y1, y2, z1, z2 >>

l3 == /\ pc = "l3"
      /\ IF y3#x2
            THEN /\ y2' = 2*y2
                 /\ y3' = (y3 \div 2)
                 /\ pc' = "l4"
            ELSE /\ pc' = "l5"
                 /\ UNCHANGED << y2, y3 >>
      /\ UNCHANGED << y1, z1, z2 >>

l4 == /\ pc = "l4"
      /\ IF y3\leq y1
            THEN /\ y1' = y1-y3
                 /\ y2' = y2+1
            ELSE /\ TRUE
                 /\ UNCHANGED << y1, y2 >>
      /\ pc' = "l3"
      /\ UNCHANGED << y3, z1, z2 >>

l5 == /\ pc = "l5"
      /\ z1' = y1
      /\ z2' = y2
      /\ pc' = "l6"
      /\ UNCHANGED << y1, y2, y3 >>

l6 == /\ pc = "l6"
      /\ PrintT(<<x1,x2,z1,z2>>)
      /\ pc' = "Done"
      /\ UNCHANGED << y1, y2, y3, z1, z2 >>

Next == l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


Qpc == pc="Done" => x1=z2*x2+z1 /\ 0 \leq z1 /\ z1 < x2
COND(U) ==   U # defaultInitValue =>  min \leq U /\ U \leq max
Qef ==  COND(y1) /\ COND(y2) /\ COND(y3) /\ COND(z1) /\ COND(z2)

Iloop(u,v)  == x1=v*x2+u

i == Iloop(y1,y2)
=============================================================================
\* Modification History
\* Last modified Mon Oct 02 15:37:38 CEST 2023 by mery
\* Created Wed Nov 18 16:33:27 CET 2015 by mery
