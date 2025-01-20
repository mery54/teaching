--------- MODULE plus --------
EXTENDS Integers,TLC
CONSTANTS x0,U (* x is the input *)


(*
--algorithm  squareroot  {
variables y1,y2,y3,z,x=x0;
{
l0:
y1:=0;y2:=0;y3:=0;
l1: while (y2 <  x){
	  l2: y1:=y1+1;y2:=y2+y3+2;y3:=y3+2;
	};
l3:z:=y1;print <<z>>;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8e96bc4d" /\ chksum(tla) = "96fc278b")
CONSTANT defaultInitValue
VARIABLES y1, y2, y3, z, x, pc

vars == << y1, y2, y3, z, x, pc >>

Init == (* Global variables *)
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ z = defaultInitValue
        /\ x = x0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ y1' = 0
      /\ y2' = 0
      /\ y3' = 0
      /\ pc' = "l1"
      /\ UNCHANGED << z, x >>

l1 == /\ pc = "l1"
      /\ IF y2 <  x
            THEN /\ pc' = "l2"
            ELSE /\ pc' = "l3"
      /\ UNCHANGED << y1, y2, y3, z, x >>

l2 == /\ pc = "l2"
      /\ y1' = y1+1
      /\ y2' = y2+y3+2
      /\ y3' = y3+2
      /\ pc' = "l1"
      /\ UNCHANGED << z, x >>

l3 == /\ pc = "l3"
      /\ z' = y1
      /\ PrintT(<<z'>>)
      /\ pc' = "Done"
      /\ UNCHANGED << y1, y2, y3, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


--------------------------------------------------------------
MAX == 32767  (* 16 bits *)
MIN == -32768
D == MIN..MAX \cup {defaultInitValue}
(*  x \leq 32760 *)
Safety_absence ==  (y1 \in D)  /\ (y2 \in D) /\ (y3  \in D) /\ (z \in D)
i ==
	/\ pc="l0" => y1 \in D  /\  y2 \in D /\  y3 \in D /\  z \in D
	/\ pc="l1" => y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  y1*y1\leq x 
	/\ pc="l2" => y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  y1*y1\leq x /\ y2 \leq x   
	/\ pc="l3" =>  y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  z*z\leq x /\ x < (z+1)*(z+1)


Safety_partialcorrectness == pc="l3" =>  y2 = (y1+1)*(y1+1) /\ y3=2*y1+1  /\  z*z\leq x /\ x < (z+1)*(z+1)

Qtermination == pc # "l5"

=========
