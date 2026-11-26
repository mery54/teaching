---------------------- MODULE tp3 --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT MAXINT,u,v 

(*
-termination
-wfNext
--algorithm Power {
  variables x1 =u; (* 1st integer *)
            x2 = v;  (* 2nd integer *)
            y1;
            y2;
            y3;
            z;
       
 
{
    l1: print <<x1, x2>>;
    
    y1:=x1;
    y2:=x2;
    y3:=1;
   l2:while (y2 /= 0) {
    
      L3:if ( y2 % 2 # 0) {
        l4:y2:=y2-1;
        l5:y3:=y3*y1;
      };
      l6:y1 := y1*y1;
      l7:y2:= y2 \div   2;
    };
    assert y2=0;
    l8: z := y3;
    l9: print <<x1, x2,z>>;
}

}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x1, x2, y1, y2, y3, z, pc

vars == << x1, x2, y1, y2, y3, z, pc >>

Init == (* Global variables *)
        /\ x1 = u
        /\ x2 = v
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ z = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ PrintT(<<x1, x2>>)
      /\ y1' = x1
      /\ y2' = x2
      /\ y3' = 1
      /\ pc' = "l2"
      /\ UNCHANGED << x1, x2, z >>

l2 == /\ pc = "l2"
      /\ IF y2 /= 0
            THEN /\ pc' = "L3"
            ELSE /\ Assert(y2=0, 
                           "Failure of assertion at line 33, column 5.")
                 /\ pc' = "l8"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

L3 == /\ pc = "L3"
      /\ IF y2 % 2 # 0
            THEN /\ pc' = "l4"
            ELSE /\ pc' = "l6"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

l4 == /\ pc = "l4"
      /\ y2' = y2-1
      /\ pc' = "l5"
      /\ UNCHANGED << x1, x2, y1, y3, z >>

l5 == /\ pc = "l5"
      /\ y3' = y3*y1
      /\ pc' = "l6"
      /\ UNCHANGED << x1, x2, y1, y2, z >>

l6 == /\ pc = "l6"
      /\ y1' = y1*y1
      /\ pc' = "l7"
      /\ UNCHANGED << x1, x2, y2, y3, z >>

l7 == /\ pc = "l7"
      /\ y2' = (y2 \div   2)
      /\ pc' = "l2"
      /\ UNCHANGED << x1, x2, y1, y3, z >>

l8 == /\ pc = "l8"
      /\ z' = y3
      /\ pc' = "l9"
      /\ UNCHANGED << x1, x2, y1, y2, y3 >>

l9 == /\ pc = "l9"
      /\ PrintT(<<x1, x2,z>>)
      /\ pc' = "Done"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

Next == l1 \/ l2 \/ L3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Q1 == pc # "Done"
Qpc == pc ="Done" => z=x1^x2
D == 0..MAXINT\cup {defaultInitValue}
Q2 ==  (*  pc # "l1" => *) y1 \in D /\ y2 \in D /\ y3 \in D /\ x1 \in D /\ x2 \in D 


==================================================================
\* Modification History
\* Last modified Mon Oct 03 09:02:48 CEST 2016 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
