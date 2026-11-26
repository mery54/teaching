--------------------- MODULE  pluscalil268q ----------------------

\* suite du module
\* ================= SERVEUR S1 =================
process S1 = 1
variable c;
begin
debut:skip;
S1loop:while TRUE do
       l1:await Len(queue1) > 0;
        l2:req1 := TRUE;
        l3:coordQ := Append(coordQ, 1);
        l4:await grant1 = TRUE ;
        l5:c := Head(queue1);
        l6:queue1 := Tail(queue1);
        \* section critique
        R := 1;
        state1[c] := "serve";
        \* print <<"S1 sert Client1", c>>;
        s1:await R = 0;
        grant1 := FALSE;
        req1 := FALSE;
    end while;
end process;

\* ================= SERVEUR S2 =================
process S2 = 2
variable c;
begin
debut:skip;
S2loop:while TRUE do
        l1:await Len(queue2) > 0;
        l2:req2 := TRUE;
        l3:coordQ := Append(coordQ, 2);
        l4:await grant2 = TRUE;
        l5:c := Head(queue2);
        l6:queue2 := Tail(queue2);
        R := 1;
        state2[c] := "serve";
        \* print <<"S2 sert Client2", c>>;
        s2: await R = 0;
        grant2 := FALSE;
        req2 := FALSE;
    end while;
end process;

\* ================= COORDONNATEUR =================
process C = 3
variable s;
begin
debut:skip;
Cloop:while TRUE do
       l1: await Len(coordQ) > 0 /\ R = 0;
        l2:s := Head(coordQ);
        l3:coordQ := Tail(coordQ);
        l4:if s = 1 then
            grant1 := TRUE;
            l5:await grant1 = FALSE;
        elsif s = 2 then
            grant2 := TRUE;
            l6:await grant2 = FALSE;
        end if;
	l7:skip;
    end while;
end process;

end algorithm; *)



============================
