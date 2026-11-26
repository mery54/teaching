------------------------------- MODULE pluscal_trib --------------------------------
EXTENDS TLC,Integers,Naturals


n == 5
t0 == [k \in 0..n-1 |->
                    IF k=0 THEN 3
                    ELSE IF k=1 THEN 6
                    ELSE IF k=2 THEN 2*k
                    ELSE IF k=3 THEN 9
                    ELSE 5]



(*
--algorithm  tribulle {
variables t,i,j,d=TRUE,temp;
{
    t:=t0;
    i:=0;
    while(i < n /\ d)
	{
		d := FALSE;
		j:= 1;
		while ( j <  (n - i))
		{
			if (t[j-1] > t[j])
			{
				temp := t[j-1];
				t[j-1] := t[j];
				t[j] := temp;
				d := TRUE;
 			};
 			j:=j+1;
		};
		i:=i+1;
	}
}

}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES t, i, j, d, temp, pc

vars == << t, i, j, d, temp, pc >>

Init == (* Global variables *)
        /\ t = defaultInitValue
        /\ i = defaultInitValue
        /\ j = defaultInitValue
        /\ d = TRUE
        /\ temp = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ t' = t0
         /\ i' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << j, d, temp >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i < n /\ d
               THEN /\ d' = FALSE
                    /\ j' = 1
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << j, d >>
         /\ UNCHANGED << t, i, temp >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF j <  (n - i)
               THEN /\ IF t[j-1] > t[j]
                          THEN /\ temp' = t[j-1]
                               /\ t' = [t EXCEPT ![j-1] = t[j]]
                               /\ pc' = "Lbl_4"
                          ELSE /\ pc' = "Lbl_5"
                               /\ UNCHANGED << t, temp >>
                    /\ i' = i
               ELSE /\ i' = i+1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << t, temp >>
         /\ UNCHANGED << j, d >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ j' = j+1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << t, i, d, temp >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ t' = [t EXCEPT ![j] = temp]
         /\ d' = TRUE
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << i, j, temp >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_5 \/ Lbl_4
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


Safe1 == pc # "Done"
Safe2 == pc="Done" => \A e \in 0..n-1: t[e] \leq t[e+1]
Safe3 == pc="Done" => { e \in 0..n-1: t[e] \leq t[e+1]} = 0..n-1
Safe4 == pc="Done" => (t[0] \leq t[1]) /\ (t[1] \leq t[2])  


====
