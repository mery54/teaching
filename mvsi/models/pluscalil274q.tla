---- MODULE pluscalil274q  -----------
\*CalculFonctions ----
EXTENDS Integers, TLC
CONSTANTS input

ASSUME 

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
    safe: assert ?????;
    print resultat;
end process;

end algorithm; *)




==== 
