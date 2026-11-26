---------------------- MODULE pluscalil273q --------------------
\* suite 
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


SafePC == .......

=========================
