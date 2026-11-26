--------------------- MODULE  pluscalil268 ----------------------
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
\* BEGIN TRANSLATION (chksum(pcal) = "e176308f" /\ chksum(tla) = "b4a9cc99")
\* Label debut of process Client1 at line 31 col 7 changed to debut_
\* Label l1 of process Client1 at line 34 col 12 changed to l1_
\* Label l2 of process Client1 at line 35 col 12 changed to l2_
\* Label l3 of process Client1 at line 37 col 12 changed to l3_
\* Label csin of process Client1 at line 39 col 14 changed to csin_
\* Label csout of process Client1 at line 42 col 15 changed to csout_
\* Label debut of process Client2 at line 50 col 7 changed to debut_C
\* Label l1 of process Client2 at line 52 col 12 changed to l1_C
\* Label l2 of process Client2 at line 53 col 12 changed to l2_C
\* Label l3 of process Client2 at line 54 col 12 changed to l3_C
\* Label debut of process S1 at line 65 col 7 changed to debut_S
\* Label l1 of process S1 at line 67 col 11 changed to l1_S
\* Label l2 of process S1 at line 68 col 12 changed to l2_S
\* Label l3 of process S1 at line 69 col 12 changed to l3_S
\* Label l4 of process S1 at line 70 col 12 changed to l4_
\* Label l5 of process S1 at line 71 col 12 changed to l5_
\* Label l6 of process S1 at line 72 col 12 changed to l6_
\* Label debut of process S2 at line 87 col 7 changed to debut_S2
\* Label l1 of process S2 at line 89 col 12 changed to l1_S2
\* Label l2 of process S2 at line 90 col 12 changed to l2_S2
\* Label l3 of process S2 at line 91 col 12 changed to l3_S2
\* Label l4 of process S2 at line 92 col 12 changed to l4_S
\* Label l5 of process S2 at line 93 col 12 changed to l5_S
\* Label l6 of process S2 at line 94 col 12 changed to l6_S
\* Process variable c of process S1 at line 63 col 10 changed to c_
CONSTANT defaultInitValue
VARIABLES R, state1, state2, queue1, queue2, coordQ, req1, req2, grant1, 
          grant2, pc, c_, c, s

vars == << R, state1, state2, queue1, queue2, coordQ, req1, req2, grant1, 
           grant2, pc, c_, c, s >>

ProcSet == (4..(3+p)) \cup ((p+4)..(p+3+q)) \cup {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ R = 0
        /\ state1 = [i \in 4..(3+p) |-> "idle"]
        /\ state2 = [i \in (p+4)..(p+3+q) |-> "idle"]
        /\ queue1 = <<>>
        /\ queue2 = <<>>
        /\ coordQ = <<>>
        /\ req1 = FALSE
        /\ req2 = FALSE
        /\ grant1 = FALSE
        /\ grant2 = FALSE
        (* Process S1 *)
        /\ c_ = defaultInitValue
        (* Process S2 *)
        /\ c = defaultInitValue
        (* Process C *)
        /\ s = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in 4..(3+p) -> "debut_"
                                        [] self \in (p+4)..(p+3+q) -> "debut_C"
                                        [] self = 1 -> "debut_S"
                                        [] self = 2 -> "debut_S2"
                                        [] self = 3 -> "debut"]

debut_(self) == /\ pc[self] = "debut_"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "C1loop"]
                /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, 
                                req1, req2, grant1, grant2, c_, c, s >>

C1loop(self) == /\ pc[self] = "C1loop"
                /\ pc' = [pc EXCEPT ![self] = "l1_"]
                /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, 
                                req1, req2, grant1, grant2, c_, c, s >>

l1_(self) == /\ pc[self] = "l1_"
             /\ state1' = [state1 EXCEPT ![self] = "requete"]
             /\ pc' = [pc EXCEPT ![self] = "l2_"]
             /\ UNCHANGED << R, state2, queue1, queue2, coordQ, req1, req2, 
                             grant1, grant2, c_, c, s >>

l2_(self) == /\ pc[self] = "l2_"
             /\ queue1' = Append(queue1, self)
             /\ pc' = [pc EXCEPT ![self] = "l3_"]
             /\ UNCHANGED << R, state1, state2, queue2, coordQ, req1, req2, 
                             grant1, grant2, c_, c, s >>

l3_(self) == /\ pc[self] = "l3_"
             /\ state1[self] = "serve"
             /\ pc' = [pc EXCEPT ![self] = "csin_"]
             /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                             req2, grant1, grant2, c_, c, s >>

csin_(self) == /\ pc[self] = "csin_"
               /\ state1' = [state1 EXCEPT ![self] = "critique"]
               /\ PrintT(<<"Client1", self, "utilise R">>)
               /\ pc' = [pc EXCEPT ![self] = "csout_"]
               /\ UNCHANGED << R, state2, queue1, queue2, coordQ, req1, req2, 
                               grant1, grant2, c_, c, s >>

csout_(self) == /\ pc[self] = "csout_"
                /\ state1' = [state1 EXCEPT ![self] = "idle"]
                /\ R' = 0
                /\ pc' = [pc EXCEPT ![self] = "outC1"]
                /\ UNCHANGED << state2, queue1, queue2, coordQ, req1, req2, 
                                grant1, grant2, c_, c, s >>

outC1(self) == /\ pc[self] = "outC1"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "C1loop"]
               /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                               req2, grant1, grant2, c_, c, s >>

Client1(self) == debut_(self) \/ C1loop(self) \/ l1_(self) \/ l2_(self)
                    \/ l3_(self) \/ csin_(self) \/ csout_(self)
                    \/ outC1(self)

debut_C(self) == /\ pc[self] = "debut_C"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "C2loop"]
                 /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, 
                                 req1, req2, grant1, grant2, c_, c, s >>

C2loop(self) == /\ pc[self] = "C2loop"
                /\ pc' = [pc EXCEPT ![self] = "l1_C"]
                /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, 
                                req1, req2, grant1, grant2, c_, c, s >>

l1_C(self) == /\ pc[self] = "l1_C"
              /\ state2' = [state2 EXCEPT ![self] = "requete"]
              /\ pc' = [pc EXCEPT ![self] = "l2_C"]
              /\ UNCHANGED << R, state1, queue1, queue2, coordQ, req1, req2, 
                              grant1, grant2, c_, c, s >>

l2_C(self) == /\ pc[self] = "l2_C"
              /\ queue2' = Append(queue2, self)
              /\ pc' = [pc EXCEPT ![self] = "l3_C"]
              /\ UNCHANGED << R, state1, state2, queue1, coordQ, req1, req2, 
                              grant1, grant2, c_, c, s >>

l3_C(self) == /\ pc[self] = "l3_C"
              /\ state2[self] = "serve"
              /\ pc' = [pc EXCEPT ![self] = "csin"]
              /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                              req2, grant1, grant2, c_, c, s >>

csin(self) == /\ pc[self] = "csin"
              /\ state2' = [state2 EXCEPT ![self] = "critique"]
              /\ PrintT(<<"Client2", self, "utilise R">>)
              /\ pc' = [pc EXCEPT ![self] = "csout"]
              /\ UNCHANGED << R, state1, queue1, queue2, coordQ, req1, req2, 
                              grant1, grant2, c_, c, s >>

csout(self) == /\ pc[self] = "csout"
               /\ state2' = [state2 EXCEPT ![self] = "idle"]
               /\ R' = 0
               /\ pc' = [pc EXCEPT ![self] = "outC2"]
               /\ UNCHANGED << state1, queue1, queue2, coordQ, req1, req2, 
                               grant1, grant2, c_, c, s >>

outC2(self) == /\ pc[self] = "outC2"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "C2loop"]
               /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                               req2, grant1, grant2, c_, c, s >>

Client2(self) == debut_C(self) \/ C2loop(self) \/ l1_C(self) \/ l2_C(self)
                    \/ l3_C(self) \/ csin(self) \/ csout(self)
                    \/ outC2(self)

debut_S == /\ pc[1] = "debut_S"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![1] = "S1loop"]
           /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                           req2, grant1, grant2, c_, c, s >>

S1loop == /\ pc[1] = "S1loop"
          /\ pc' = [pc EXCEPT ![1] = "l1_S"]
          /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                          req2, grant1, grant2, c_, c, s >>

l1_S == /\ pc[1] = "l1_S"
        /\ Len(queue1) > 0
        /\ pc' = [pc EXCEPT ![1] = "l2_S"]
        /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                        grant1, grant2, c_, c, s >>

l2_S == /\ pc[1] = "l2_S"
        /\ req1' = TRUE
        /\ pc' = [pc EXCEPT ![1] = "l3_S"]
        /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req2, 
                        grant1, grant2, c_, c, s >>

l3_S == /\ pc[1] = "l3_S"
        /\ coordQ' = Append(coordQ, 1)
        /\ pc' = [pc EXCEPT ![1] = "l4_"]
        /\ UNCHANGED << R, state1, state2, queue1, queue2, req1, req2, grant1, 
                        grant2, c_, c, s >>

l4_ == /\ pc[1] = "l4_"
       /\ grant1 = TRUE
       /\ pc' = [pc EXCEPT ![1] = "l5_"]
       /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                       grant1, grant2, c_, c, s >>

l5_ == /\ pc[1] = "l5_"
       /\ c_' = Head(queue1)
       /\ pc' = [pc EXCEPT ![1] = "l6_"]
       /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                       grant1, grant2, c, s >>

l6_ == /\ pc[1] = "l6_"
       /\ queue1' = Tail(queue1)
       /\ R' = 1
       /\ state1' = [state1 EXCEPT ![c_] = "serve"]
       /\ pc' = [pc EXCEPT ![1] = "s1"]
       /\ UNCHANGED << state2, queue2, coordQ, req1, req2, grant1, grant2, c_, 
                       c, s >>

s1 == /\ pc[1] = "s1"
      /\ R = 0
      /\ grant1' = FALSE
      /\ req1' = FALSE
      /\ pc' = [pc EXCEPT ![1] = "S1loop"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req2, grant2, 
                      c_, c, s >>

S1 == debut_S \/ S1loop \/ l1_S \/ l2_S \/ l3_S \/ l4_ \/ l5_ \/ l6_ \/ s1

debut_S2 == /\ pc[2] = "debut_S2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![2] = "S2loop"]
            /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                            req2, grant1, grant2, c_, c, s >>

S2loop == /\ pc[2] = "S2loop"
          /\ pc' = [pc EXCEPT ![2] = "l1_S2"]
          /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                          req2, grant1, grant2, c_, c, s >>

l1_S2 == /\ pc[2] = "l1_S2"
         /\ Len(queue2) > 0
         /\ pc' = [pc EXCEPT ![2] = "l2_S2"]
         /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                         grant1, grant2, c_, c, s >>

l2_S2 == /\ pc[2] = "l2_S2"
         /\ req2' = TRUE
         /\ pc' = [pc EXCEPT ![2] = "l3_S2"]
         /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, 
                         grant1, grant2, c_, c, s >>

l3_S2 == /\ pc[2] = "l3_S2"
         /\ coordQ' = Append(coordQ, 2)
         /\ pc' = [pc EXCEPT ![2] = "l4_S"]
         /\ UNCHANGED << R, state1, state2, queue1, queue2, req1, req2, grant1, 
                         grant2, c_, c, s >>

l4_S == /\ pc[2] = "l4_S"
        /\ grant2 = TRUE
        /\ pc' = [pc EXCEPT ![2] = "l5_S"]
        /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                        grant1, grant2, c_, c, s >>

l5_S == /\ pc[2] = "l5_S"
        /\ c' = Head(queue2)
        /\ pc' = [pc EXCEPT ![2] = "l6_S"]
        /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                        grant1, grant2, c_, s >>

l6_S == /\ pc[2] = "l6_S"
        /\ queue2' = Tail(queue2)
        /\ R' = 1
        /\ state2' = [state2 EXCEPT ![c] = "serve"]
        /\ pc' = [pc EXCEPT ![2] = "s2"]
        /\ UNCHANGED << state1, queue1, coordQ, req1, req2, grant1, grant2, c_, 
                        c, s >>

s2 == /\ pc[2] = "s2"
      /\ R = 0
      /\ grant2' = FALSE
      /\ req2' = FALSE
      /\ pc' = [pc EXCEPT ![2] = "S2loop"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, grant1, 
                      c_, c, s >>

S2 == debut_S2 \/ S2loop \/ l1_S2 \/ l2_S2 \/ l3_S2 \/ l4_S \/ l5_S \/ l6_S
         \/ s2

debut == /\ pc[3] = "debut"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![3] = "Cloop"]
         /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                         grant1, grant2, c_, c, s >>

Cloop == /\ pc[3] = "Cloop"
         /\ pc' = [pc EXCEPT ![3] = "l1"]
         /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                         grant1, grant2, c_, c, s >>

l1 == /\ pc[3] = "l1"
      /\ Len(coordQ) > 0 /\ R = 0
      /\ pc' = [pc EXCEPT ![3] = "l2"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                      grant1, grant2, c_, c, s >>

l2 == /\ pc[3] = "l2"
      /\ s' = Head(coordQ)
      /\ pc' = [pc EXCEPT ![3] = "l3"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                      grant1, grant2, c_, c >>

l3 == /\ pc[3] = "l3"
      /\ coordQ' = Tail(coordQ)
      /\ pc' = [pc EXCEPT ![3] = "l4"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, req1, req2, grant1, 
                      grant2, c_, c, s >>

l4 == /\ pc[3] = "l4"
      /\ IF s = 1
            THEN /\ grant1' = TRUE
                 /\ pc' = [pc EXCEPT ![3] = "l5"]
                 /\ UNCHANGED grant2
            ELSE /\ IF s = 2
                       THEN /\ grant2' = TRUE
                            /\ pc' = [pc EXCEPT ![3] = "l6"]
                       ELSE /\ pc' = [pc EXCEPT ![3] = "l7"]
                            /\ UNCHANGED grant2
                 /\ UNCHANGED grant1
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                      c_, c, s >>

l5 == /\ pc[3] = "l5"
      /\ grant1 = FALSE
      /\ pc' = [pc EXCEPT ![3] = "l7"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                      grant1, grant2, c_, c, s >>

l6 == /\ pc[3] = "l6"
      /\ grant2 = FALSE
      /\ pc' = [pc EXCEPT ![3] = "l7"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                      grant1, grant2, c_, c, s >>

l7 == /\ pc[3] = "l7"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![3] = "Cloop"]
      /\ UNCHANGED << R, state1, state2, queue1, queue2, coordQ, req1, req2, 
                      grant1, grant2, c_, c, s >>

C == debut \/ Cloop \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == S1 \/ S2 \/ C
           \/ (\E self \in 4..(3+p): Client1(self))
           \/ (\E self \in (p+4)..(p+3+q): Client2(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 




SET1 ==  4..(3+p)
SET2 ==  (p+4)..(p+3+q)
defcs1(k) == \A  i \in SET1: i # k  => state1[i] # "critique"
defcs21  ==  \A  i \in SET2: state2[i] # "critique"
safe1 ==   \A self \in SET1: state1[self] = "critique" =>  defcs1(self) /\ defcs21



defcs2(k) == \A  i \in SET2: i # k  => state2[i] # "critique"
defcs22  ==  \A  i \in SET1: state1[i] # "critique"
safe2 ==   \A self \in SET2: state2[self] = "critique" =>  defcs2(self) /\ defcs22

safemutex == safe1 /\ safe2


aC1 == \A self \in 4..(3+p)  :state1[self] # "critique"
aC2 == \A self  \in (p+4)..(p+3+q):state2[self] # "critique"
grantS1 == grant1 = FALSE
grantS2 == grant2 = FALSE
============================
