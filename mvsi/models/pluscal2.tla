---------------------- MODULE pluscal2 --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT n
 
 f == [k \in 0..n-1 |->
                    IF k=0 THEN 3
                    ELSE IF k=1 THEN 6
                    ELSE IF k=2 THEN 2*k
                    ELSE IF k=3 THEN 9
                    ELSE 5]


(*
-termination
-wfNext
--algorithm Maximum {
  variables i = 0;
            m=0;
{
            l0:m:=f[0];
            l1: i:=1;
            l2: while (i<n) {
            l3: if (f[i]>m){
            l4: m:=f[i];
            l5: skip;
            } ;
            l6:i:=i+1;
            l7: print <<m,i>>;
            };
            l8:skip
}
           
            }
*)
\* BEGIN TRANSLATION
VARIABLES i, m, pc

vars == << i, m, pc >>

Init == (* Global variables *)
        /\ i = 0
        /\ m = 0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ m' = f[0]
      /\ pc' = "l1"
      /\ i' = i

l1 == /\ pc = "l1"
      /\ i' = 1
      /\ pc' = "l2"
      /\ m' = m

l2 == /\ pc = "l2"
      /\ IF i<n
            THEN /\ pc' = "l3"
            ELSE /\ pc' = "l8"
      /\ UNCHANGED << i, m >>

l3 == /\ pc = "l3"
      /\ IF f[i]>m
            THEN /\ pc' = "l4"
            ELSE /\ pc' = "l6"
      /\ UNCHANGED << i, m >>

l4 == /\ pc = "l4"
      /\ m' = f[i]
      /\ pc' = "l5"
      /\ i' = i

l5 == /\ pc = "l5"
      /\ TRUE
      /\ pc' = "l6"
      /\ UNCHANGED << i, m >>

l6 == /\ pc = "l6"
      /\ i' = i+1
      /\ pc' = "l7"
      /\ m' = m

l7 == /\ pc = "l7"
      /\ PrintT(<<m,i>>)
      /\ pc' = "l2"
      /\ UNCHANGED << i, m >>

l8 == /\ pc = "l8"
      /\ TRUE
      /\ pc' = "Done"
      /\ UNCHANGED << i, m >>

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
===============
