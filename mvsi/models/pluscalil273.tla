---------------------- MODULE pluscalil273 --------------------
\* CalculParalleleCanaux ----
EXTENDS Integers,Sequences,TLC
CONSTANTS
	special \* symbole spécial de marque de fin

(*--algorithm SommeCanaux

variables
    A = <<1,2,3,4,5,6,7,8>>, \* affectation des données
    chan1 = <<>>, chan2 = <<>>, chan3 = <<>>, \* canaux  de communication
    chanR = <<>>,   \* canal  des  résultats
    eod = special,
     total = 0;
\* --------------== DISTRIBUTEUR ---------------------!
process P0 = "Distributeur"
variable i = 1;
begin
   w: while i <= Len(A) do
        if i % 3 = 1 then
            chan1 := Append(chan1, A[i]);
        elsif i % 3 = 2 then
            chan2 := Append(chan2, A[i]);
        else
            chan3 := Append(chan3, A[i]);
        end if;
        i := i + 1;
    end while;

    \* fin de données
    chan1 := Append(chan1, eod);
    chan2 := Append(chan2, eod);
    chan3 := Append(chan3, eod);
end process;

\* ---------------------  P1 --------------------- !
process P1 = "P1"
variable x, sum = 0;
begin
    w:while TRUE do
        await Len(chan1) > 0;
        x := Head(chan1);
        chan1 := Tail(chan1);

        if x = eod then goto Send1;
        else sum := sum + x;
        end if;
    end while;

Send1:
    chanR := Append(chanR, sum);
end process;

\* ---------------------  P2 --------------------- !
process P2 = "P2"
variable x, sum = 0;
begin
    w:while TRUE do
        await Len(chan2) > 0;
        x := Head(chan2);
        chan2 := Tail(chan2);

        if x = eod then goto Send2;
        else sum := sum + x;
        end if;
    end while;

Send2:
    chanR := Append(chanR, sum);
end process;

\* --------------------- P3 --------------------- !
process P3 = "P3"
variable x, sum = 0;
begin
    w:while TRUE do
        await Len(chan3) > 0;
        x := Head(chan3);
        chan3 := Tail(chan3);

        if x = eod then goto Send3;
        else sum := sum + x;
        end if;
    end while;

Send3:
    chanR := Append(chanR, sum);
end process;

\* ---------------------  COMBINAISON --------------------- !
process Combine = "Combine"
variable x, count = 0;
begin
   w: while count < 3 do
        await Len(chanR) > 0;
        x := Head(chanR);
        chanR := Tail(chanR);

        total := total + x;
        count := count + 1;
    end while;

    print <<"Somme totale:", total>>;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e0b5d055" /\ chksum(tla) = "edc2539")
\* Label w of process P0 at line 19 col 7 changed to w_
\* Label w of process P1 at line 40 col 7 changed to w_P
\* Label w of process P2 at line 58 col 7 changed to w_P2
\* Label w of process P3 at line 76 col 7 changed to w_P3
\* Process variable x of process P1 at line 38 col 10 changed to x_
\* Process variable sum of process P1 at line 38 col 13 changed to sum_
\* Process variable x of process P2 at line 56 col 10 changed to x_P
\* Process variable sum of process P2 at line 56 col 13 changed to sum_P
\* Process variable x of process P3 at line 74 col 10 changed to x_P3
CONSTANT defaultInitValue
VARIABLES A, chan1, chan2, chan3, chanR, eod, total, pc, i, x_, sum_, x_P, 
          sum_P, x_P3, sum, x, count

vars == << A, chan1, chan2, chan3, chanR, eod, total, pc, i, x_, sum_, x_P, 
           sum_P, x_P3, sum, x, count >>

ProcSet == {"Distributeur"} \cup {"P1"} \cup {"P2"} \cup {"P3"} \cup {"Combine"}

Init == (* Global variables *)
        /\ A = <<1,2,3,4,5,6,7,8>>
        /\ chan1 = <<>>
        /\ chan2 = <<>>
        /\ chan3 = <<>>
        /\ chanR = <<>>
        /\ eod = special
        /\ total = 0
        (* Process P0 *)
        /\ i = 1
        (* Process P1 *)
        /\ x_ = defaultInitValue
        /\ sum_ = 0
        (* Process P2 *)
        /\ x_P = defaultInitValue
        /\ sum_P = 0
        (* Process P3 *)
        /\ x_P3 = defaultInitValue
        /\ sum = 0
        (* Process Combine *)
        /\ x = defaultInitValue
        /\ count = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Distributeur" -> "w_"
                                        [] self = "P1" -> "w_P"
                                        [] self = "P2" -> "w_P2"
                                        [] self = "P3" -> "w_P3"
                                        [] self = "Combine" -> "w"]

w_ == /\ pc["Distributeur"] = "w_"
      /\ IF i <= Len(A)
            THEN /\ IF i % 3 = 1
                       THEN /\ chan1' = Append(chan1, A[i])
                            /\ UNCHANGED << chan2, chan3 >>
                       ELSE /\ IF i % 3 = 2
                                  THEN /\ chan2' = Append(chan2, A[i])
                                       /\ chan3' = chan3
                                  ELSE /\ chan3' = Append(chan3, A[i])
                                       /\ chan2' = chan2
                            /\ chan1' = chan1
                 /\ i' = i + 1
                 /\ pc' = [pc EXCEPT !["Distributeur"] = "w_"]
            ELSE /\ chan1' = Append(chan1, eod)
                 /\ chan2' = Append(chan2, eod)
                 /\ chan3' = Append(chan3, eod)
                 /\ pc' = [pc EXCEPT !["Distributeur"] = "Done"]
                 /\ i' = i
      /\ UNCHANGED << A, chanR, eod, total, x_, sum_, x_P, sum_P, x_P3, sum, x, 
                      count >>

P0 == w_

w_P == /\ pc["P1"] = "w_P"
       /\ Len(chan1) > 0
       /\ x_' = Head(chan1)
       /\ chan1' = Tail(chan1)
       /\ IF x_' = eod
             THEN /\ pc' = [pc EXCEPT !["P1"] = "Send1"]
                  /\ sum_' = sum_
             ELSE /\ sum_' = sum_ + x_'
                  /\ pc' = [pc EXCEPT !["P1"] = "w_P"]
       /\ UNCHANGED << A, chan2, chan3, chanR, eod, total, i, x_P, sum_P, x_P3, 
                       sum, x, count >>

Send1 == /\ pc["P1"] = "Send1"
         /\ chanR' = Append(chanR, sum_)
         /\ pc' = [pc EXCEPT !["P1"] = "Done"]
         /\ UNCHANGED << A, chan1, chan2, chan3, eod, total, i, x_, sum_, x_P, 
                         sum_P, x_P3, sum, x, count >>

P1 == w_P \/ Send1

w_P2 == /\ pc["P2"] = "w_P2"
        /\ Len(chan2) > 0
        /\ x_P' = Head(chan2)
        /\ chan2' = Tail(chan2)
        /\ IF x_P' = eod
              THEN /\ pc' = [pc EXCEPT !["P2"] = "Send2"]
                   /\ sum_P' = sum_P
              ELSE /\ sum_P' = sum_P + x_P'
                   /\ pc' = [pc EXCEPT !["P2"] = "w_P2"]
        /\ UNCHANGED << A, chan1, chan3, chanR, eod, total, i, x_, sum_, x_P3, 
                        sum, x, count >>

Send2 == /\ pc["P2"] = "Send2"
         /\ chanR' = Append(chanR, sum_P)
         /\ pc' = [pc EXCEPT !["P2"] = "Done"]
         /\ UNCHANGED << A, chan1, chan2, chan3, eod, total, i, x_, sum_, x_P, 
                         sum_P, x_P3, sum, x, count >>

P2 == w_P2 \/ Send2

w_P3 == /\ pc["P3"] = "w_P3"
        /\ Len(chan3) > 0
        /\ x_P3' = Head(chan3)
        /\ chan3' = Tail(chan3)
        /\ IF x_P3' = eod
              THEN /\ pc' = [pc EXCEPT !["P3"] = "Send3"]
                   /\ sum' = sum
              ELSE /\ sum' = sum + x_P3'
                   /\ pc' = [pc EXCEPT !["P3"] = "w_P3"]
        /\ UNCHANGED << A, chan1, chan2, chanR, eod, total, i, x_, sum_, x_P, 
                        sum_P, x, count >>

Send3 == /\ pc["P3"] = "Send3"
         /\ chanR' = Append(chanR, sum)
         /\ pc' = [pc EXCEPT !["P3"] = "Done"]
         /\ UNCHANGED << A, chan1, chan2, chan3, eod, total, i, x_, sum_, x_P, 
                         sum_P, x_P3, sum, x, count >>

P3 == w_P3 \/ Send3

w == /\ pc["Combine"] = "w"
     /\ IF count < 3
           THEN /\ Len(chanR) > 0
                /\ x' = Head(chanR)
                /\ chanR' = Tail(chanR)
                /\ total' = total + x'
                /\ count' = count + 1
                /\ pc' = [pc EXCEPT !["Combine"] = "w"]
           ELSE /\ PrintT(<<"Somme totale:", total>>)
                /\ pc' = [pc EXCEPT !["Combine"] = "Done"]
                /\ UNCHANGED << chanR, total, x, count >>
     /\ UNCHANGED << A, chan1, chan2, chan3, eod, i, x_, sum_, x_P, sum_P, 
                     x_P3, sum >>

Combine == w

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == P0 \/ P1 \/ P2 \/ P3 \/ Combine
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



=========================
