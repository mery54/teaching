--------- MODULE pluscal_squareroot --------
EXTENDS Integers,TLC
CONSTANTS x  (* x is the input *)
--------------------------------------------------------------

(*
--algorithm  squareroot {
variables y1,y2,y3,z;
{
l0: assert (y1 = defaultInitValue /\ y2 = defaultInitValue /\ y3 = defaultInitValue /\ z = defaultInitValue);
y1:=0;y2:=1;y3:=1;
l1: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x;
l:while (y2 \leq x){
    l2: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y2  \leq x;
    y1:=y1+1;
    y2:=y2+y3+2; y3:=y3+2;
    l3: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x;
    
    };
l4: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x /\ x < y2;
z:=y1;
l5: print <<x,z,y1,y2,y3>>;
    }
 }

*)
\* BEGIN TRANSLATION (chksum(pcal) = "d6c5dbb6" /\ chksum(tla) = "48b1ccaa")
CONSTANT defaultInitValue
VARIABLES y1, y2, y3, z, pc

vars == << y1, y2, y3, z, pc >>

Init == (* Global variables *)
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ z = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert((y1 = defaultInitValue /\ y2 = defaultInitValue /\ y3 = defaultInitValue /\ z = defaultInitValue), 
                "Failure of assertion at line 10, column 5.")
      /\ y1' = 0
      /\ y2' = 1
      /\ y3' = 1
      /\ pc' = "l1"
      /\ z' = z

l1 == /\ pc = "l1"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x, 
                "Failure of assertion at line 12, column 5.")
      /\ pc' = "l"
      /\ UNCHANGED << y1, y2, y3, z >>

l == /\ pc = "l"
     /\ IF y2 \leq x
           THEN /\ pc' = "l2"
           ELSE /\ pc' = "l4"
     /\ UNCHANGED << y1, y2, y3, z >>

l2 == /\ pc = "l2"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y2  \leq x, 
                "Failure of assertion at line 14, column 9.")
      /\ y1' = y1+1
      /\ y2' = y2+y3+2
      /\ y3' = y3+2
      /\ pc' = "l3"
      /\ z' = z

l3 == /\ pc = "l3"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x, 
                "Failure of assertion at line 17, column 9.")
      /\ pc' = "l"
      /\ UNCHANGED << y1, y2, y3, z >>

l4 == /\ pc = "l4"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x /\ x < y2, 
                "Failure of assertion at line 20, column 5.")
      /\ z' = y1
      /\ pc' = "l5"
      /\ UNCHANGED << y1, y2, y3 >>

l5 == /\ pc = "l5"
      /\ PrintT(<<x,z,y1,y2,y3>>)
      /\ pc' = "Done"
      /\ UNCHANGED << y1, y2, y3, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l \/ l2 \/ l3 \/ l4 \/ l5
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


MAX == 32768  (* 16 bits *)
D == 0..MAX
(*  x \leq 32768 *)
DD(X) ==  ( X # defaultInitValue =>  X \in D)
init(X) ==  ( X # defaultInitValue)

Safety_absence ==  DD(y1)  /\ DD(y2) /\ DD(y3) /\ DD(z)

Safety_partialcorrectness == pc="Done" =>  z*z\leq x /\ x < (z+1)*(z+1)

Inv == 
    /\ pc \in {"l","l0","l1","l2","l3","l4","Done","l5","l33"}
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

=========
