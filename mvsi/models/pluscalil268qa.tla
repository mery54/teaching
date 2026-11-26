--------------------- MODULE  pluscalil268q ----------------------
EXTENDS Integers, Sequences,TLC
------------------------------------------------------------------
CONSTANTS p, q  
------------------------------------------------------------------
ASSUME  
------------------------------------------------------------------
(*--algorithm Mutex

variables
    R = ?, \* 0 libre, 1 occupée
    \* états des clients
    state1 = [i \in 4..(3+p) |-> "idle"],
    state2 = [i \in (p+4)..(p+3+q) |-> "idle"],
    \* files FIFO des clients
    queue1 = <<>>,
    queue2 = <<>>,
    \* file FIFO des serveurs
    coordQ = <<>>,
    req1 = ?,
    req2 = ?,
    grant1 = ?,
    grant2 = ?;

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


============================
