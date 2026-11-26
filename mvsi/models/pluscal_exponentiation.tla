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

--  algorithm Power {
  variables 
            x1=x10;
	    x2=x20;
	    y1;
            y2;
            y3;
            z;
{
    l0: assert x1=x10 /\ x2=x20 /\ typeInt(x1)/\ typeInt(x2) /\ typeInt(y1) /\ typeInt(y2) /\ typeInt(y3) /\ typeInbt(z);
    print <<x1, x2>>;
    y1:=x1;
    y2:=x2;
    y3:=1;   
   l1: assert x1=x10 /\ x2 = x20 /\  y2 \geq 0  /\ y3* y1^y2 = x1^x2 /\ typeInt(x1)/\ typeInt(x2) /\ typeInt(y1) /\ typeInt(y2) /\ typeInt(y3) /\ typeInt(z);

while (y2 /= 0) {
    
      l2: assert y2 \neq 0 /\ y3* y1^y2 = x1^x2 /\ /\ typeInt(x1)/\ typeInt(x2) /\ typeInt(y1) /\ typeInt(y2) /\ typeInt(y3) /\ typeInt(z);



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


L == {"l0","l1"}
D == MININT..MAXINT

DD(X) == X=defaultInitValue => X \in D

i == 
    /\ pc \in L
    /\ DD(y1) /\ DD(y2) /\ DD(y3) /\ DD(z)
    /\ pc="l1" => x1=x10 /\ x2 = x20 /\  y2 \geq 0  /\ y3* y1^y2 = x1^x2 /\ /\ typeInt(x1)/\ typeInt(x2) /\ typeInt(y1) /\ typeInt(y2) /\ typeInt(y3) /\ typeInbt(z)
Q1 == pc # "Done"
Qpc == pc ="Done" => z=x1^x2


==================================================================
\* Modification History
\* Last modified Fri Dec 15 08:00:00 CET 2017 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
