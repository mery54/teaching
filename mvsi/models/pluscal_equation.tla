-------------------------------- MODULE pluscal_equation --------------------------------
EXTENDS TLC,Integers,Naturals,Reals

CONSTANTS a0,b0,c0
(*

--algorithm resolution {
variables a=a0, b=b0, c=c0, determinant;
{
  
  l0:determinant:=b*b-4*a*c;
  if (determinant>0)
  {
      
      l1:print <<"Two Roots are:">>;
  }
  else if (determinant=0)
  {
    
    l2:print <<"One Double roots are:">>;
  }
  else
  {
    
    l3:print <<"Two complex Roots are:">>;
  }
  }
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES a, b, c, determinant, pc

vars == << a, b, c, determinant, pc >>

Init == (* Global variables *)
        /\ a = a0
        /\ b = b0
        /\ c = c0
        /\ determinant = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ determinant' = b*b-4*a*c
      /\ IF determinant'>0
            THEN /\ pc' = "l1"
            ELSE /\ IF determinant'=0
                       THEN /\ pc' = "l2"
                       ELSE /\ pc' = "l3"
      /\ UNCHANGED << a, b, c >>

l1 == /\ pc = "l1"
      /\ PrintT(<<"Two Roots are:">>)
      /\ pc' = "Done"
      /\ UNCHANGED << a, b, c, determinant >>

l2 == /\ pc = "l2"
      /\ PrintT(<<"One Double roots are:">>)
      /\ pc' = "Done"
      /\ UNCHANGED << a, b, c, determinant >>

l3 == /\ pc = "l3"
      /\ PrintT(<<"Two complex Roots are:">>)
      /\ pc' = "Done"
      /\ UNCHANGED << a, b, c, determinant >>

Next == l0 \/ l1 \/ l2 \/ l3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Fri Mar 23 14:44:05 CET 2018 by mery
\* Created Wed Nov 18 16:33:27 CET 2015 by mery
