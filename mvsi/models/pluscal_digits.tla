-------------------------------- MODULE pluscal_digits -------------------------
EXTENDS TLC,Integers,Naturals
CONSTANTS n0,MMIN,MMAX

(*
--algorithm  compte{
variables n, count=0;
{
  l0:n:=n0;
  l1:while (n#0)
  {  
     l2: n:= n \div 10;        
      l3:count := count +1;
  };
  l4:print <<"Number of digits: %d",count>>;
}
}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, count, pc

vars == << n, count, pc >>

Init == (* Global variables *)
        /\ n = defaultInitValue
        /\ count = 0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ n' = n0
      /\ pc' = "l1"
      /\ count' = count

l1 == /\ pc = "l1"
      /\ IF n#0
            THEN /\ pc' = "l2"
            ELSE /\ pc' = "l4"
      /\ UNCHANGED << n, count >>

l2 == /\ pc = "l2"
      /\ n' = (n \div 10)
      /\ pc' = "l3"
      /\ count' = count

l3 == /\ pc = "l3"
      /\ count' = count +1
      /\ pc' = "l1"
      /\ n' = n

l4 == /\ pc = "l4"
      /\ PrintT(<<"Number of digits: %d",count>>)
      /\ pc' = "Done"
      /\ UNCHANGED << n, count >>

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
D == MMIN..MMAX
test1 == pc="Done" /\ n0=345  =>  count = 3
test2 == pc="Done" /\ n0=0  =>  count = 0
safe ==  n # defaultInitValue =>  0 \leq n /\ n \leq n0
safepc == 
    /\ n0=0 => (count = 1) 
    /\ n0 # 0 => (\A i \in D: (10^{i-1}) \leq n0 /\ n0 \leq ((10^i)-1) => (count=i))
======================


