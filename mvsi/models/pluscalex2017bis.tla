-------------------------- MODULE pluscalex2017bis --------------------------
EXTENDS Naturals, Integers, TLC
-----------------------------------------------------
T=={"triangle","rectangle"}
S == [i \in 1..5 |->  IF (i=1) THEN "triangle"
                        ELSE IF (i=2) THEN "triangle"
                        ELSE IF (i=3) THEN "rectangle"
                        ELSE "triangle"]
                        
D1 == [i \in 1..5 |-> IF (i=1) THEN 3
                        ELSE IF (i=2) THEN 3
                        ELSE IF (i=3) THEN 3
                        ELSE 3]
                        

D2 == [i \in 1..5 |-> IF (i=1) THEN 2
                        ELSE IF (i=2) THEN 2
                        ELSE IF (i=3) THEN 8
                        ELSE 10]
                        
aire0 == [i \in 1..5 |-> 0]
--------------------------------------------------------
(*
--fair algorithm ex {
  variables  i = 1; s=0;aire = aire0;
  {
    l0: while (i<=5) {
    l1: if (S[i]="triangle") 
    {aire[i]:=(D1[i]*D2[i]) \div 2;}
    else
    {aire[i]:=D1[i]*D2[i];};
     l3:s:=s + aire[i];
     l4:i:=i+1;
     };
     
    l5: print <<aire,S,s>>;
}

}
*)
\* BEGIN TRANSLATION
VARIABLES i, s, aire, pc

vars == << i, s, aire, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ s = 0
        /\ aire = aire0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ IF i<=5
            THEN /\ pc' = "l1"
            ELSE /\ pc' = "l5"
      /\ UNCHANGED << i, s, aire >>

l1 == /\ pc = "l1"
      /\ IF S[i]="triangle"
            THEN /\ aire' = [aire EXCEPT ![i] = (D1[i]*D2[i]) \div 2]
            ELSE /\ aire' = [aire EXCEPT ![i] = D1[i]*D2[i]]
      /\ pc' = "l3"
      /\ UNCHANGED << i, s >>

l3 == /\ pc = "l3"
      /\ s' = s + aire[i]
      /\ pc' = "l4"
      /\ UNCHANGED << i, aire >>

l4 == /\ pc = "l4"
      /\ i' = i+1
      /\ pc' = "l0"
      /\ UNCHANGED << s, aire >>

l5 == /\ pc = "l5"
      /\ PrintT(<<aire,S,s>>)
      /\ pc' = "Done"
      /\ UNCHANGED << i, s, aire >>

Next == l0 \/ l1 \/ l3 \/ l4 \/ l5
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Dec 13 22:48:23 CET 2017 by mery
\* Created Wed Dec 13 22:19:19 CET 2017 by mery
