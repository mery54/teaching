--------- MODULE pluscal_cubic --------
EXTENDS Integers,TLC
CONSTANTS x  (* x is the input *)
--------------------------------------------------------------

(*
-wfNext
--algorithm  cube  {
variables z=0,v=0,w=1,t=3,u=0;
{
l0:skip;
w:while (u <  x){
	  l1:
	  z:=z+v+w;
	  l3:
	  v:=v+t;
	  l4:
	  t:=t+6;
	  l5:
	  w:=w+3;
	  l6:
	  u:=u+1;
	  l7:skip;
	};
l2:print <<z>>;
}
}
}
*)
\* BEGIN TRANSLATION
\* Label w at line 12 col 3 changed to w_
VARIABLES z, v, w, t, u, pc

vars == << z, v, w, t, u, pc >>

Init == (* Global variables *)
        /\ z = 0
        /\ v = 0
        /\ w = 1
        /\ t = 3
        /\ u = 0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ TRUE
      /\ pc' = "w_"
      /\ UNCHANGED << z, v, w, t, u >>

w_ == /\ pc = "w_"
      /\ IF u <  x
            THEN /\ pc' = "l1"
            ELSE /\ pc' = "l2"
      /\ UNCHANGED << z, v, w, t, u >>

l1 == /\ pc = "l1"
      /\ z' = z+v+w
      /\ pc' = "l3"
      /\ UNCHANGED << v, w, t, u >>

l3 == /\ pc = "l3"
      /\ v' = v+t
      /\ pc' = "l4"
      /\ UNCHANGED << z, w, t, u >>

l4 == /\ pc = "l4"
      /\ t' = t+6
      /\ pc' = "l5"
      /\ UNCHANGED << z, v, w, u >>

l5 == /\ pc = "l5"
      /\ w' = w+3
      /\ pc' = "l6"
      /\ UNCHANGED << z, v, t, u >>

l6 == /\ pc = "l6"
      /\ u' = u+1
      /\ pc' = "l7"
      /\ UNCHANGED << z, v, w, t >>

l7 == /\ pc = "l7"
      /\ TRUE
      /\ pc' = "w_"
      /\ UNCHANGED << z, v, w, t, u >>

l2 == /\ pc = "l2"
      /\ PrintT(<<z>>)
      /\ pc' = "Done"
      /\ UNCHANGED << z, v, w, t, u >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ w_ \/ l1 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION




MAX == 32768  (* 16 bits *)
D == 0..32768
(*  x \leq 32760 *)
(*
DD(X) == (X # defaultInitValue => X \in D)

Safety_absence ==  DD(y1)  /\ DD(y2) /\ DD(y3) /\ DD(z)

*)


Safety_partialcorrectness == pc="Done" => z=x*x*x
Inv == 
    pc \in {"l0","w","l1","l2"} 
    =>
    /\ w=3*u+1
    /\ v=3*u^2
    /\ z+v+w=(u+1)^3
    /\ v+t=3*(u+1)^2
    /\ t=3*(2*u+1)
    
    
Il3 == 
    pc="l3"
    =>
    /\ w=3*u+1
    /\ v=3*u^2
    /\ z=(u+1)^3
    /\ v+t=3*(u+1)^2
    
    
Il4 == 
    pc="l4"
    =>
    /\ w=3*u+1
    /\ v=3*(u+1)^2
    /\ z=(u+1)^3
    /\ v=3*(u+1)^2
    

Il5 == 
    pc="l5"
    =>
    /\ w=3*u+1
    /\ v=3*(u+1)^2
    /\ z=(u+1)^3
    /\ v=3*(u+1)^2
    
 Il6 == 
    pc="l6"
    =>
    /\ w=3*(u+1)+1
    /\ v=3*(u+1)^2
    /\ z=(u+1)^3
    /\ v=3*(u+1)^2
  
  
Il7 == 
    pc="l7"
    =>
    /\ w=3*u+1
    /\ v=3*u^2
    /\ z+v+w=(u+1)^3
    /\ v+t=3*(u+1)^2
    /\ z=u^3
    
Il2 == pc="l2" => z=x^3
      
test ==  Safety_partialcorrectness
Safety1 ==  Inv /\ Il4 /\ Il5 /\ Il6 /\ Il7
Safety ==  Inv /\ Il3 /\ Il4 /\ Il5 /\ Il6 /\ Il2

=========
