----------------------------- MODULE pluscal254 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS n

(*

--algorithm ex3{ 
variables x = 1..n,y,z,es=0,os=0,s = 0;


process (zero = 0)
{
  A: await x = {} ;
  B: assert x={};
  C: s := es + os;
  print <<s>>;
};

process (E = 2)
{
  E: while (x # {})
  {
    F:y := CHOOSE v \in 1..n: v \in x; 
    G: if (y % 2 = 0) { es:= es + y; x := x  \  {y};};
   };
  print <<es>>; 
};


process (O = 1)
{
  E: while (x # {})
  {
    F: z := CHOOSE v \in 1..n: v \in x; 
    G: if (z  % 2 # 0) { os:= os + z; x := x  \  {z};};
   };
  print <<os>>; 
};



}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "2162a5e4" /\ chksum(tla) = "b7b0f2cf")
\* Label E of process E at line 21 col 6 changed to E_
\* Label F of process E at line 23 col 7 changed to F_
\* Label G of process E at line 24 col 8 changed to G_
\* Label E of process O at line 32 col 6 changed to E_O
CONSTANT defaultInitValue
VARIABLES x, y, z, es, os, s, pc

vars == << x, y, z, es, os, s, pc >>

ProcSet == {0} \cup {2} \cup {1}

Init == (* Global variables *)
        /\ x = 1..n
        /\ y = defaultInitValue
        /\ z = defaultInitValue
        /\ es = 0
        /\ os = 0
        /\ s = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "A"
                                        [] self = 2 -> "E_"
                                        [] self = 1 -> "E_O"]

A == /\ pc[0] = "A"
     /\ x = {}
     /\ pc' = [pc EXCEPT ![0] = "B"]
     /\ UNCHANGED << x, y, z, es, os, s >>

B == /\ pc[0] = "B"
     /\ Assert(x={}, "Failure of assertion at line 14, column 6.")
     /\ pc' = [pc EXCEPT ![0] = "C"]
     /\ UNCHANGED << x, y, z, es, os, s >>

C == /\ pc[0] = "C"
     /\ s' = es + os
     /\ PrintT(<<s'>>)
     /\ pc' = [pc EXCEPT ![0] = "Done"]
     /\ UNCHANGED << x, y, z, es, os >>

zero == A \/ B \/ C

E_ == /\ pc[2] = "E_"
      /\ IF x # {}
            THEN /\ pc' = [pc EXCEPT ![2] = "F_"]
            ELSE /\ PrintT(<<es>>)
                 /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << x, y, z, es, os, s >>

F_ == /\ pc[2] = "F_"
      /\ y' = (CHOOSE v \in 1..n: v \in x)
      /\ pc' = [pc EXCEPT ![2] = "G_"]
      /\ UNCHANGED << x, z, es, os, s >>

G_ == /\ pc[2] = "G_"
      /\ IF y % 2 = 0
            THEN /\ es' = es + y
                 /\ x' = x  \  {y}
            ELSE /\ TRUE
                 /\ UNCHANGED << x, es >>
      /\ pc' = [pc EXCEPT ![2] = "E_"]
      /\ UNCHANGED << y, z, os, s >>

E == E_ \/ F_ \/ G_

E_O == /\ pc[1] = "E_O"
       /\ IF x # {}
             THEN /\ pc' = [pc EXCEPT ![1] = "F"]
             ELSE /\ PrintT(<<os>>)
                  /\ pc' = [pc EXCEPT ![1] = "Done"]
       /\ UNCHANGED << x, y, z, es, os, s >>

F == /\ pc[1] = "F"
     /\ z' = (CHOOSE v \in 1..n: v \in x)
     /\ pc' = [pc EXCEPT ![1] = "G"]
     /\ UNCHANGED << x, y, es, os, s >>

G == /\ pc[1] = "G"
     /\ IF z  % 2 # 0
           THEN /\ os' = os + z
                /\ x' = x  \  {z}
           ELSE /\ TRUE
                /\ UNCHANGED << x, os >>
     /\ pc' = [pc EXCEPT ![1] = "E_O"]
     /\ UNCHANGED << y, z, es, s >>

O == E_O \/ F \/ G

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == zero \/ E \/ O
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

P1 == pc[1]="Done" => x={}
P2 == pc[2]="Done" /\ pc[1]="Done" => s = (n*(n+1)) \div  2
P3 == pc[2]="Done" => es = (n \div  2)*(n \div 2 +1)
P4 == pc[2]="Done" => os = ((n+1) \div  2)*((n+1) \div 2 )
test == P2



====
