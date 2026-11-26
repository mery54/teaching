-------------------------------- MODULE pluscal_td6ex2 --------------------------------
EXTENDS TLC,Integers,Naturals
CONSTANTS x1,x2,MMIN,MMAX



(*
--algorithm  division {
variables y1,y2,y3,z1,z2;
{
    l0:y1:=x1;
    l1:y2:=0;
    l2:y3:=x2;
    l3: while (y3 \leq y1) {l33:y3:=2*y3;}; 
    l4:while (y3 # x2) 
    {
    l5:y2 := 2*y2;
	l6:y3:=y3 \div 2;
	l7:if (y3 \leq y1 )
            {
            l8:y1:=y1 - y3;
            l9:y2:=y2+1;
            };
     };
      l10:z1:=y1;
      l11:z2:=y2;
      l12:skip;}            
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
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ y1' = x1
      /\ pc' = "l1"
      /\ UNCHANGED << y2, y3, z1, z2 >>

l1 == /\ pc = "l1"
      /\ y2' = 0
      /\ pc' = "l2"
      /\ UNCHANGED << y1, y3, z1, z2 >>

l2 == /\ pc = "l2"
      /\ y3' = x2
      /\ pc' = "l3"
      /\ UNCHANGED << y1, y2, z1, z2 >>

l3 == /\ pc = "l3"
      /\ IF y3 \leq y1
            THEN /\ pc' = "l33"
            ELSE /\ pc' = "l4"
      /\ UNCHANGED << y1, y2, y3, z1, z2 >>

l33 == /\ pc = "l33"
       /\ y3' = 2*y3
       /\ pc' = "l3"
       /\ UNCHANGED << y1, y2, z1, z2 >>

l4 == /\ pc = "l4"
      /\ IF y3 # x2
            THEN /\ pc' = "l5"
            ELSE /\ pc' = "l10"
      /\ UNCHANGED << y1, y2, y3, z1, z2 >>

l5 == /\ pc = "l5"
      /\ y2' = 2*y2
      /\ pc' = "l6"
      /\ UNCHANGED << y1, y3, z1, z2 >>

l6 == /\ pc = "l6"
      /\ y3' = (y3 \div 2)
      /\ pc' = "l7"
      /\ UNCHANGED << y1, y2, z1, z2 >>

l7 == /\ pc = "l7"
      /\ IF y3 \leq y1
            THEN /\ pc' = "l8"
            ELSE /\ pc' = "l4"
      /\ UNCHANGED << y1, y2, y3, z1, z2 >>

l8 == /\ pc = "l8"
      /\ y1' = y1 - y3
      /\ pc' = "l9"
      /\ UNCHANGED << y2, y3, z1, z2 >>

l9 == /\ pc = "l9"
      /\ y2' = y2+1
      /\ pc' = "l4"
      /\ UNCHANGED << y1, y3, z1, z2 >>

l10 == /\ pc = "l10"
       /\ z1' = y1
       /\ pc' = "l11"
       /\ UNCHANGED << y1, y2, y3, z2 >>

l11 == /\ pc = "l11"
       /\ z2' = y2
       /\ pc' = "l12"
       /\ UNCHANGED << y1, y2, y3, z1 >>

l12 == /\ pc = "l12"
       /\ TRUE
       /\ pc' = "Done"
       /\ UNCHANGED << y1, y2, y3, z1, z2 >>

Next == l0 \/ l1 \/ l2 \/ l3 \/ l33 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9
           \/ l10 \/ l11 \/ l12
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


SAFEPC == pc="Done" => (x1=z2*x2+z1) /\ ( 0 \leq z1 /\ z1 < x2) 

RTE(X) == X=defaultInitValue \/ (MMIN \leq X /\ X \leq MMAX)  

SAFERTE ==
    /\ RTE(y1)
    /\ RTE(y2)
    /\ RTE(y3)
    /\ RTE(z1)
    /\ RTE(z2)

=====


