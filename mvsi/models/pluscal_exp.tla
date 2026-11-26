---------------------- MODULE pluscal_exp --------------------------------
EXTENDS Naturals, Integers, TLC
--------------------------------------------
CONSTANT MAXINT,x10,x20,MININT 
----------------------
typeInt(u) == u \in Int 
pre == x10 \in Nat /\ x20 \in Nat /\ x10 # 0
------------------------------------------------------------------
(* precondition *)
ASSUME pre
-------------------------------------------------------
(*
--algorithm Power {
  variables 
            x1=x10;
	    x2=x20;
	    y1;
            y2;
            y3;
            z;
{
    l0: 
    y1:=x1; y2:=x2; y3:=1;   
    w:while (y2 /= 0) {
    
      l2: 

if ( y2 % 2 # 0) {
        l3:y2:=y2-1;
        l4:y3:=y3*y1;
        l5:skip;
      };
      l6:y1 := y1*y1;      l7:y2:= y2 \div   2;
      l8:skip;
    };
    l9: z := y3;
    l10: print <<x1, x2,z>>;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c28c1999" /\ chksum(tla) = "f9286308")
CONSTANT defaultInitValue
VARIABLES x1, x2, y1, y2, y3, z, pc

vars == << x1, x2, y1, y2, y3, z, pc >>

Init == (* Global variables *)
        /\ x1 = x10
        /\ x2 = x20
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ z = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ y1' = x1
      /\ y2' = x2
      /\ y3' = 1
      /\ pc' = "w"
      /\ UNCHANGED << x1, x2, z >>

w == /\ pc = "w"
     /\ IF y2 /= 0
           THEN /\ pc' = "l2"
           ELSE /\ pc' = "l9"
     /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

l2 == /\ pc = "l2"
      /\ IF y2 % 2 # 0
            THEN /\ pc' = "l3"
            ELSE /\ pc' = "l6"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

l3 == /\ pc = "l3"
      /\ y2' = y2-1
      /\ pc' = "l4"
      /\ UNCHANGED << x1, x2, y1, y3, z >>

l4 == /\ pc = "l4"
      /\ y3' = y3*y1
      /\ pc' = "l5"
      /\ UNCHANGED << x1, x2, y1, y2, z >>

l5 == /\ pc = "l5"
      /\ TRUE
      /\ pc' = "l6"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

l6 == /\ pc = "l6"
      /\ y1' = y1*y1
      /\ pc' = "l7"
      /\ UNCHANGED << x1, x2, y2, y3, z >>

l7 == /\ pc = "l7"
      /\ y2' = (y2 \div   2)
      /\ pc' = "l8"
      /\ UNCHANGED << x1, x2, y1, y3, z >>

l8 == /\ pc = "l8"
      /\ TRUE
      /\ pc' = "w"
      /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

l9 == /\ pc = "l9"
      /\ z' = y3
      /\ pc' = "l10"
      /\ UNCHANGED << x1, x2, y1, y2, y3 >>

l10 == /\ pc = "l10"
       /\ PrintT(<<x1, x2,z>>)
       /\ pc' = "Done"
       /\ UNCHANGED << x1, x2, y1, y2, y3, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ w \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9 \/ l10
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



L == {"l0","l1"}
D == MININT..MAXINT

DD(X) == X=defaultInitValue => X \in D

i == 
    /\ pc \in L
    /\ DD(y1) /\ DD(y2) /\ DD(y3) /\ DD(z)
    /\ typeInt(x1)/\ typeInt(x2) /\ typeInt(y1) /\ typeInt(y2) /\ typeInt(y3) /\ typeInt(z)
    /\ pc="y0" => x1=x10 /\ x2=x20
    /\ pc="l1" => x1=x10 /\ x2 = x20 /\  y2 \geq 0  /\ y3* y1^y2 = x1^x2 
    /\  pc = "w" => x1=x10 /\ x2 = x20 /\  y2 \geq 0  /\ y3* y1^y2 = x1^x2
    /\ pc="l2" =>  y2 # 0 /\ y3* y1^y2 = x1^x2 




Q1 == pc # "Done"
Qpc == pc ="Done" => z=x1^x2

==================================================================
\* Modification History
\* Last modified Thu Mar 28 23:16:14 CET 2024 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
