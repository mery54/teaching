--------- MODULE pluscal_power3 --------
EXTENDS Integers,TLC
CONSTANTS x  (* x is the input *)
--------------------------------------------------------------

(*
--algorithm  squareroot {
variables cz=0,cv=0,cw=1,ct=3,k=0,r;
{

l1:  assert k \geq 0 /\ cz = k*k*k  /\ cv+ct = 3*(k+1)*(k+1)
     /\ cz+cv+cw = (k+1)*(k+1)*(k+1) /\ cv = 3*k*k  /\ cw = 3*k+1;
in: while (k<x)
	{
l2: assert   k \geq 0 /\   k <  x /\ cz = k*k*k  /\ cv+ct = 3*(k+1)*(k+1)
    /\ cz+cv+cw = (k+1)*(k+1)*(k+1) /\ cv = 3*k*k  /\ cw = 3*k+1;
	  cz:=cz+cv+cw;
l3: assert   k \geq 0 /\   k <  x /\cz = (k+1)*(k+1)*(k+1)  /\ cv+ct = 3*(k+1)*(k+1)
    /\ cz = (k+1)*(k+1)*(k+1) /\ cv = 3*k*k  /\ cw = 3*k+1;	  
	  cv:=cv+ct;
l4: assert   k \geq 0 /\   k <  x /\ cz = (k+1)*(k+1)*(k+1)  /\ cv = 3*(k+1)*(k+1)
    /\ cz = (k+1)*(k+1)*(k+1)   /\ cw = 3*k+1;	  	  
	  ct:=ct+6;
l5: assert   k \geq 0 /\   k <  x /\ cz = (k+1)*(k+1)*(k+1)  /\ cv = 3*(k+1)*(k+1)
    /\ cz = (k+1)*(k+1)*(k+1)   /\ cw = 3*k+1 /\ cv+ct = 3*(k+2)*(k+2);	  	  	  
	  cw:=cw+3;
l6: assert   k \geq 0 /\   k <  x /\ cz = (k+1)*(k+1)*(k+1)  /\ cv = 3*(k+1)*(k+1)
    /\ cz+cv+cw = (k+2)*(k+2)*(k+2)   /\ cw = 3*(k+1)+1 /\ cv+ct = 3*(k+2)*(k+2);	  	  	  	  
	  k:=k+1;
l7: assert   k \geq 0 /\   k \leq  x /\ cz = (k)*(k)*(k)  /\ cv = 3*(k)*(k)
    /\ cz+cv+cw = (k+1)*(k+1)*(k+1)   /\ cw = 3*(k)+1 /\ cv+ct = 3*(k+1)*(k+1);	  	  	  	  	  
	  };
l8: assert k=x /\  cz = (k)*(k)*(k)  /\ cv = 3*(k)*(k) /\ cz+cv+cw = (k+1)*(k+1)*(k+1)
    /\ cw = 3*(k)+1 /\ cv+ct = 3*(k+1)*(k+1);	  	  	  	  	  	  
  r:=cz;
l9: assert r=cz /\ k=x/\  cz = (k)*(k)*(k)  /\ cv = 3*(k)*(k)
    /\ cz+cv+cw = (k+1)*(k+1)*(k+1) /\ cw = 3*(k)+1 /\ cv+ct = 3*(k+1)*(k+1);	  	  	  	  	    
l58: print <<x,r>>;
    }
 }

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES cz, cv, cw, ct, k, r, pc

vars == << cz, cv, cw, ct, k, r, pc >>

Init == (* Global variables *)
        /\ cz = 0
        /\ cv = 0
        /\ cw = 1
        /\ ct = 3
        /\ k = 0
        /\ r = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(       k \geq 0 /\ cz = k*k*k  /\ cv+ct = 3*(k+1)*(k+1)
                /\ cz+cv+cw = (k+1)*(k+1)*(k+1) /\ cv = 3*k*k  /\ cw = 3*k+1, 
                "Failure of assertion at line 11, column 6.")
      /\ pc' = "in"
      /\ UNCHANGED << cz, cv, cw, ct, k, r >>

in == /\ pc = "in"
      /\ IF k<x
            THEN /\ pc' = "l2"
            ELSE /\ pc' = "l8"
      /\ UNCHANGED << cz, cv, cw, ct, k, r >>

l2 == /\ pc = "l2"
      /\ Assert(         k \geq 0 /\   k <  x /\ cz = k*k*k  /\ cv+ct = 3*(k+1)*(k+1)
                /\ cz+cv+cw = (k+1)*(k+1)*(k+1) /\ cv = 3*k*k  /\ cw = 3*k+1, 
                "Failure of assertion at line 15, column 5.")
      /\ cz' = cz+cv+cw
      /\ pc' = "l3"
      /\ UNCHANGED << cv, cw, ct, k, r >>

l3 == /\ pc = "l3"
      /\ Assert(         k \geq 0 /\   k <  x /\cz = (k+1)*(k+1)*(k+1)  /\ cv+ct = 3*(k+1)*(k+1)
                /\ cz = (k+1)*(k+1)*(k+1) /\ cv = 3*k*k  /\ cw = 3*k+1, 
                "Failure of assertion at line 18, column 5.")
      /\ cv' = cv+ct
      /\ pc' = "l4"
      /\ UNCHANGED << cz, cw, ct, k, r >>

l4 == /\ pc = "l4"
      /\ Assert(         k \geq 0 /\   k <  x /\ cz = (k+1)*(k+1)*(k+1)  /\ cv = 3*(k+1)*(k+1)
                /\ cz = (k+1)*(k+1)*(k+1)   /\ cw = 3*k+1, 
                "Failure of assertion at line 21, column 5.")
      /\ ct' = ct+6
      /\ pc' = "l5"
      /\ UNCHANGED << cz, cv, cw, k, r >>

l5 == /\ pc = "l5"
      /\ Assert(         k \geq 0 /\   k <  x /\ cz = (k+1)*(k+1)*(k+1)  /\ cv = 3*(k+1)*(k+1)
                /\ cz = (k+1)*(k+1)*(k+1)   /\ cw = 3*k+1 /\ cv+ct = 3*(k+2)*(k+2), 
                "Failure of assertion at line 24, column 5.")
      /\ cw' = cw+3
      /\ pc' = "l6"
      /\ UNCHANGED << cz, cv, ct, k, r >>

l6 == /\ pc = "l6"
      /\ Assert(         k \geq 0 /\   k <  x /\ cz = (k+1)*(k+1)*(k+1)  /\ cv = 3*(k+1)*(k+1)
                /\ cz+cv+cw = (k+2)*(k+2)*(k+2)   /\ cw = 3*(k+1)+1 /\ cv+ct = 3*(k+2)*(k+2), 
                "Failure of assertion at line 27, column 5.")
      /\ k' = k+1
      /\ pc' = "l7"
      /\ UNCHANGED << cz, cv, cw, ct, r >>

l7 == /\ pc = "l7"
      /\ Assert(         k \geq 0 /\   k \leq  x /\ cz = (k)*(k)*(k)  /\ cv = 3*(k)*(k)
                /\ cz+cv+cw = (k+1)*(k+1)*(k+1)   /\ cw = 3*(k)+1 /\ cv+ct = 3*(k+1)*(k+1), 
                "Failure of assertion at line 30, column 5.")
      /\ pc' = "in"
      /\ UNCHANGED << cz, cv, cw, ct, k, r >>

l8 == /\ pc = "l8"
      /\ Assert(       k=x /\  cz = (k)*(k)*(k)  /\ cv = 3*(k)*(k) /\ cz+cv+cw = (k+1)*(k+1)*(k+1)
                /\ cw = 3*(k)+1 /\ cv+ct = 3*(k+1)*(k+1), 
                "Failure of assertion at line 33, column 5.")
      /\ r' = cz
      /\ pc' = "l9"
      /\ UNCHANGED << cz, cv, cw, ct, k >>

l9 == /\ pc = "l9"
      /\ Assert(       r=cz /\ k=x/\  cz = (k)*(k)*(k)  /\ cv = 3*(k)*(k)
                /\ cz+cv+cw = (k+1)*(k+1)*(k+1) /\ cw = 3*(k)+1 /\ cv+ct = 3*(k+1)*(k+1), 
                "Failure of assertion at line 36, column 5.")
      /\ pc' = "l58"
      /\ UNCHANGED << cz, cv, cw, ct, k, r >>

l58 == /\ pc = "l58"
       /\ PrintT(<<x,r>>)
       /\ pc' = "Done"
       /\ UNCHANGED << cz, cv, cw, ct, k, r >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ in \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9 \/ l58
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=========

MAX == 32768  (* 16 bits *)
D == 0..MAX
(*  x \leq 32768 *)
DD(X) ==  ( X # defaultInitValue =>  X \in D)
init(X) ==  ( X # defaultInitValue)

Safety_absence ==  DD(y1)  /\ DD(y2) /\ DD(y3) /\ DD(z)

Safety_partialcorrectness == pc="Done" =>  z*z\leq x /\ x < (z+1)*(z+1)

Inv == 
    /\ pc \in {"l0","l1","l2","l3","l4","Done","l5","l33"}
    /\  (init(y1) /\ init(y2) /\ init(y3) /\ init(z)) => (y1 \in Nat /\ y2 \in Nat /\ y3 \in Nat /\ z \in Nat)
    /\ pc = "l0" =>  (y1 = defaultInitValue /\ y2 = defaultInitValue /\ y3 = defaultInitValue /\ z = defaultInitValue)
    /\ pc = "l1"  => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x
    /\ pc = "l2" => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y2  \leq x
    /\ pc="l3" => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x
    /\ pc="l4" => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x /\ x < y2
    /\ Safety_partialcorrectness 

check ==  
    /\ Safety_absence
    /\ Safety_partialcorrectness
    /\ Inv
