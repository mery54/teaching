---- MODULE pluscalil270  ----
EXTENDS Integers, Sequences,TLC

(*--algorithm Tri



procedure InsertSort(seq)
variable i, j, tmp;
begin
    i := 2;
    while i <= Len(seq) do
        j := i;
        while j > 1 /\ seq[j] < seq[j-1] do
            tmp := seq[j];
            seq[j] := seq[j-1];
            seq[j-1] := tmp;
            j := j - 1;
        end while;
        i := i + 1;
    end while;
    return(seq);
end procedure;


variables
    inputs = <<5,2,8,1,7,3,6>>,

    chan1 = <<>>, chan2 = <<>>, chan3 = <<>>,
    chanF1 = <<>>, chanF2 = <<>>, chanF3 = <<>>,

    eod = -1; \* marqueur fin

\* ================= PROCESSUS P1 =================
process P1 = "P1"
variable i = 1;
begin
P1_loop:
    while i <= Len(inputs) do
        if i % 3 = 1 then
            chan1 := Append(chan1, inputs[i]);
        elsif i % 3 = 2 then
            chan2 := Append(chan2, inputs[i]);
        else
            chan3 := Append(chan3, inputs[i]);
        end if;
        i := i + 1;
    end while;

    \* envoyer fin
    chan1 := Append(chan1, eod);
    chan2 := Append(chan2, eod);
    chan3 := Append(chan3, eod);
end process;

\* ================= Q1 =================
process Q1 = "Q1"
variable local = <<>>, x;
begin
Q1_loop:
    while TRUE do
        await Len(chan1) > 0;
        x := Head(chan1);
        chan1 := Tail(chan1);

        if x = eod then
            goto Sort1;
        else
            local := Append(local, x);
        end if;
    end while;

Sort1:
    \* tri simple (insertion)
    local := InsertionSort(local);

    \* envoyer au fusion
    sortloop1: while Len(local) > 0 do
        chanF1 := Append(chanF1, Head(local));
        local := Tail(local);
    end while;

    chanF1 := Append(chanF1, eod);
end process;

\* ================= Q2 =================
process Q2 = "Q2"
variable local = <<>>, x;
begin
Q2_loop:
    while TRUE do
        await Len(chan2) > 0;
        x := Head(chan2);
        chan2 := Tail(chan2);

        if x = eod then
            goto Sort2;
        else
            local := Append(local, x);
        end if;
    end while;

Sort2:
    local := SortSeq(local);

    sortloop2:while Len(local) > 0 do
        chanF2 := Append(chanF2, Head(local));
        local := Tail(local);
    end while;

    chanF2 := Append(chanF2, eod);
end process;

\* ================= Q3 =================
process Q3 = "Q3"
variable local = <<>>, x;
begin
Q3_loop:
    while TRUE do
        await Len(chan3) > 0;
        x := Head(chan3);
        chan3 := Tail(chan3);

        if x = eod then
            goto Sort3;
        else
            local := Append(local, x);
        end if;
    end while;

Sort3:
    local := SortSeq(local);

    sortloop3:while Len(local) > 0 do
        chanF3 := Append(chanF3, Head(local));
        local := Tail(local);
    end while;

    chanF3 := Append(chanF3, eod);
end process;

\* ================= FUSION =================
process Fusion = "Fusion"
variables x1 = -1, x2 = -1, x3 = -1,
          done1 = FALSE, done2 = FALSE, done3 = FALSE,
          result = <<>>;
begin
Fusion_loop:
    while ~(done1 /\ done2 /\ done3) do

        if ~done1 /\ x1 = -1 then
            await Len(chanF1) > 0;
            x1 := Head(chanF1);
            chanF1 := Tail(chanF1);
            if x1 = eod then done1 := TRUE; end if;
        end if;

        if ~done2 /\ x2 = -1 then
            await Len(chanF2) > 0;
            x2 := Head(chanF2);
            chanF2 := Tail(chanF2);
            if x2 = eod then done2 := TRUE; end if;
        end if;

        if ~done3 /\ x3 = -1 then
            await Len(chanF3) > 0;
            x3 := Head(chanF3);
            chanF3 := Tail(chanF3);
            if x3 = eod then done3 := TRUE; end if;
        end if;

        \* choisir le minimum
        if ~done1 \/ ~done2 \/ ~done3 then
            if (done2 \/ x1 <= x2) /\ (done3 \/ x1 <= x3) then
                result := Append(result, x1);
                l1:x1 := -1;
            elsif (done1 \/ x2 <= x1) /\ (done3 \/ x2 <= x3) then
                result := Append(result, x2);
               l2: x2 := -1;
            else
                result := Append(result, x3);
                l3:x3 := -1;
            end if;
        end if;

    end while;
    print <<"Resultat trie:", result>>;
end process;

end algorithm; *)
====