-------------------------------- MODULE pluscal5 --------------------------------
EXTENDS TLC,Integers,Naturals
CONSTANTS n0,min,max

(*
--algorithm  compte{
variables n=n0, reverse=0, rem,temp,r;
{
  l1:temp:=n;
  w:while (temp#0)
  {  
     l2:rem := temp % 10;
     l3:reverse:= reverse*10+rem;
     l4:temp := temp \div 10;
  };
  l5:print <<"finde  boucle">>;
  if (reverse=n)   {
    print <<"palin",n>>;
    r:=TRUE;
    }
    else
    {
    print <<"not palin",n>>;
    r:=FALSE;
    }

}
}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, reverse, rem, temp, r, pc

vars == << n, reverse, rem, temp, r, pc >>

Init == (* Global variables *)
        /\ n = n0
        /\ reverse = 0
        /\ rem = defaultInitValue
        /\ temp = defaultInitValue
        /\ r = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ temp' = n
      /\ pc' = "w"
      /\ UNCHANGED << n, reverse, rem, r >>

w == /\ pc = "w"
     /\ IF temp#0
           THEN /\ pc' = "l2"
           ELSE /\ pc' = "l5"
     /\ UNCHANGED << n, reverse, rem, temp, r >>

l2 == /\ pc = "l2"
      /\ rem' = temp % 10
      /\ pc' = "l3"
      /\ UNCHANGED << n, reverse, temp, r >>

l3 == /\ pc = "l3"
      /\ reverse' = reverse*10+rem
      /\ pc' = "l4"
      /\ UNCHANGED << n, rem, temp, r >>

l4 == /\ pc = "l4"
      /\ temp' = (temp \div 10)
      /\ pc' = "w"
      /\ UNCHANGED << n, reverse, rem, r >>

l5 == /\ pc = "l5"
      /\ PrintT(<<"finde  boucle">>)
      /\ IF reverse=n
            THEN /\ PrintT(<<"palin",n>>)
                 /\ r' = TRUE
            ELSE /\ PrintT(<<"not palin",n>>)
                 /\ r' = FALSE
      /\ pc' = "Done"
      /\ UNCHANGED << n, reverse, rem, temp >>

Next == l1 \/ w \/ l2 \/ l3 \/ l4 \/ l5
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

D == min..max
DD(X)== (X=defaultInitValue) \/ (X \in D)

question1 == pc="Done" => (r=TRUE => reverse=n)
question2 == DD(reverse) /\ DD(temp)









P1 == n \in D /\ reverse \in D /\ (rem =  \/ rem \in D) /\ (temp =defaultInitValue \/ temp \in D )


======================


