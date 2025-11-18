-------------------------------- MODULE appex4_11 --------------------------------
EXTENDS TLC,Integers,Naturals
CONSTANTS n0
n == 5
t0 == [k \in 0..n-1 |->
                    IF k=0 THEN 3
                    ELSE IF k=1 THEN 6
                    ELSE IF k=2 THEN 2*k
                    ELSE IF k=3 THEN 9
                    ELSE 5]



(*
--algorithm  triselection {
variables i, mini, j, x,t;
{
    t:=t0;
    i:=0;
    while(i < n )
    {
        mini := i;
        j:= i;
        while ( j <  n)
        {
            if (t[j] < t[mini])
            {
                mini:= j;
                 };
            x:=t[i];
            t[i]:=t[mini];
            t[mini]:=x;
            
            j:=j+1;
        };
        i:=i+1;
    }
}

}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES i, mini, j, x, t, pc

vars == << i, mini, j, x, t, pc >>

Init == (* Global variables *)
        /\ i = defaultInitValue
        /\ mini = defaultInitValue
        /\ j = defaultInitValue
        /\ x = defaultInitValue
        /\ t = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ t' = t0
         /\ i' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << mini, j, x >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i < n
               THEN /\ mini' = i
                    /\ j' = i
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << mini, j >>
         /\ UNCHANGED << i, x, t >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF j <  n
               THEN /\ IF t[j] < t[mini]
                          THEN /\ mini' = j
                          ELSE /\ TRUE
                               /\ mini' = mini
                    /\ x' = t[i]
                    /\ t' = [t EXCEPT ![i] = t[mini']]
                    /\ pc' = "Lbl_4"
                    /\ i' = i
               ELSE /\ i' = i+1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << mini, x, t >>
         /\ j' = j

Lbl_4 == /\ pc = "Lbl_4"
         /\ t' = [t EXCEPT ![mini] = x]
         /\ j' = j+1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << i, mini, x >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION





======================


