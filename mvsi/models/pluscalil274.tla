---- MODULE pluscalil274  -----------
\*CalculFonctions ----
EXTENDS Integers, TLC
CONSTANTS input

ASSUME input \geq 0

(* --algorithm calcul
variables 
    x = input, 
    r1 = 0, r2 = 0, r3 = 0,
    done1 = FALSE, done2 = FALSE, done3 = FALSE,
    demande1 = FALSE, demande2 = FALSE, demande3 = FALSE,
    resultat = 0;

process  P1 = "P1"
begin
P1_loop:
    while (TRUE) do
        if (demande1 = TRUE) then
            r1 := 5 * x * x * x;
            done1 := TRUE;
            demande1 := FALSE;
        end if;
    end while;
end process;

process P2 = "P2"
begin
P2_loop:
    while (TRUE) do
        if (demande2 = TRUE) then
            r2 := x * x;
            done2 := TRUE;
            demande2 := FALSE;
        end if;
    end while;
end process;

process P3 = "P3"
begin
P3_loop:
    while (TRUE) do
        if (demande3 = TRUE) then
            r3 := 6 * (x + 2) * (x + 2);
            done3 := TRUE;
            demande3 := FALSE;
        end if;
    end while;
end process;

process P4 = "Coordinateur"
begin
    l1: demande1 := TRUE;
    demande2 := TRUE;
    demande3 := TRUE;

Attente:
    while ~(done1 /\ done2 /\ done3) do
        skip;
    end while;

    resultat := r1 + r2 + r3;
    assert resultat = 5 * x * x * x +  x * x + 6 * (x + 2) * (x + 2);
    print resultat;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "423d7d1b" /\ chksum(tla) = "584cfc6d")
VARIABLES x, r1, r2, r3, done1, done2, done3, demande1, demande2, demande3, 
          resultat, pc

vars == << x, r1, r2, r3, done1, done2, done3, demande1, demande2, demande3, 
           resultat, pc >>

ProcSet == {"P1"} \cup {"P2"} \cup {"P3"} \cup {"Coordinateur"}

Init == (* Global variables *)
        /\ x = input
        /\ r1 = 0
        /\ r2 = 0
        /\ r3 = 0
        /\ done1 = FALSE
        /\ done2 = FALSE
        /\ done3 = FALSE
        /\ demande1 = FALSE
        /\ demande2 = FALSE
        /\ demande3 = FALSE
        /\ resultat = 0
        /\ pc = [self \in ProcSet |-> CASE self = "P1" -> "P1_loop"
                                        [] self = "P2" -> "P2_loop"
                                        [] self = "P3" -> "P3_loop"
                                        [] self = "Coordinateur" -> "l1"]

P1_loop == /\ pc["P1"] = "P1_loop"
           /\ IF (demande1 = TRUE)
                 THEN /\ r1' = 5 * x * x * x
                      /\ done1' = TRUE
                      /\ demande1' = FALSE
                 ELSE /\ TRUE
                      /\ UNCHANGED << r1, done1, demande1 >>
           /\ pc' = [pc EXCEPT !["P1"] = "P1_loop"]
           /\ UNCHANGED << x, r2, r3, done2, done3, demande2, demande3, 
                           resultat >>

P1 == P1_loop

P2_loop == /\ pc["P2"] = "P2_loop"
           /\ IF (demande2 = TRUE)
                 THEN /\ r2' = x * x
                      /\ done2' = TRUE
                      /\ demande2' = FALSE
                 ELSE /\ TRUE
                      /\ UNCHANGED << r2, done2, demande2 >>
           /\ pc' = [pc EXCEPT !["P2"] = "P2_loop"]
           /\ UNCHANGED << x, r1, r3, done1, done3, demande1, demande3, 
                           resultat >>

P2 == P2_loop

P3_loop == /\ pc["P3"] = "P3_loop"
           /\ IF (demande3 = TRUE)
                 THEN /\ r3' = 6 * (x + 2) * (x + 2)
                      /\ done3' = TRUE
                      /\ demande3' = FALSE
                 ELSE /\ TRUE
                      /\ UNCHANGED << r3, done3, demande3 >>
           /\ pc' = [pc EXCEPT !["P3"] = "P3_loop"]
           /\ UNCHANGED << x, r1, r2, done1, done2, demande1, demande2, 
                           resultat >>

P3 == P3_loop

l1 == /\ pc["Coordinateur"] = "l1"
      /\ demande1' = TRUE
      /\ demande2' = TRUE
      /\ demande3' = TRUE
      /\ pc' = [pc EXCEPT !["Coordinateur"] = "Attente"]
      /\ UNCHANGED << x, r1, r2, r3, done1, done2, done3, resultat >>

Attente == /\ pc["Coordinateur"] = "Attente"
           /\ IF ~(done1 /\ done2 /\ done3)
                 THEN /\ TRUE
                      /\ pc' = [pc EXCEPT !["Coordinateur"] = "Attente"]
                      /\ UNCHANGED resultat
                 ELSE /\ resultat' = r1 + r2 + r3
                      /\ Assert(resultat' = 5 * x * x * x +  x * x + 6 * (x + 2) * (x + 2), 
                                "Failure of assertion at line 64, column 5.")
                      /\ PrintT(resultat')
                      /\ pc' = [pc EXCEPT !["Coordinateur"] = "Done"]
           /\ UNCHANGED << x, r1, r2, r3, done1, done2, done3, demande1, 
                           demande2, demande3 >>

P4 == l1 \/ Attente

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == P1 \/ P2 \/ P3 \/ P4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 





==== 
