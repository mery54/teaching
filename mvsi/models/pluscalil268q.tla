--------------------- MODULE  pluscalil268q ----------------------
EXTENDS Integers, Sequences,TLC
------------------------------------------------------------------
CONSTANTS p, q  \* ,m,n
------------------------------------------------------------------
ASSUME  p \in Nat /\ q \in Nat /\ p # 0 /\ q # 0

\* C1 = A == [i \in 4..(3+p) |-> m*i % n]
\* C2 = A == [i \in (p+4)..(p+3+q) |-> n*i % m]
------------------------------------------------------------------
(*--algorithm Mutex

variables
    R = 0, \* 0 libre, 1 occupée
    \* états des clients
    state1 = [i \in 4..(3+p) |-> "idle"],
    state2 = [i \in (p+4)..(p+3+q) |-> "idle"],
    \* files FIFO des clients
    queue1 = <<>>,
    queue2 = <<>>,
    \* file FIFO des serveurs
    coordQ = <<>>,
    req1 = FALSE,
    req2 = FALSE,
    grant1 = FALSE,
    grant2 = FALSE;

\* ================= CLIENTS TYPE 1 =================
process Client1 \in 4..(3+p)
begin
debut:skip;
C1loop: while TRUE do
        \* idle -> requête
        l1:state1[self] := "requete";
        l2:queue1 := Append(queue1, self);
        \* attendre d'être servi
        l3:await state1[self] = "serve";
        \* utilisation ressource
        csin:state1[self] := "critique";
        print <<"Client1", self, "utilise R">>;
        \* libération
        csout:state1[self] := "idle"; R:=0;
	outC1:skip;
    end while;
end process;

\* ================= CLIENTS TYPE 2 =================
process Client2 \in (p+4)..(p+3+q)
begin
debut:skip;
C2loop:while TRUE do
        l1:state2[self] := "requete";
        l2:queue2 := Append(queue2, self);
        l3:await state2[self] = "serve";
        csin:state2[self] := "critique";
        print <<"Client2", self, "utilise R">>;
        csout:state2[self] := "idle";  R:=0;
		outC2:skip;
    end while;
end process;
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
