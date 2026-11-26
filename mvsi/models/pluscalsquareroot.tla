--------- MODULE pluscal_squareroot --------
EXTENDS Integers,TLC
CONSTANTS x  (* x is the input *)
--------------------------------------------------------------

(*
--algorithm  squareroot {
variables y1,y2,y3,z;
{
l0:y1:=0;y2:=1;y3:=1;
l1: while (y2 \leq x){
    l2: y1:=y1+1;
    y2:=y2+y3+2; y3:=y3+2;
    l3: skip;
    
    };
l4: z:=y1;
l5: print <<x,z,y1,y2,y3>>;
    }
 }

*)
\* BEGIN TRANSLATION
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
      /\ y1' = 0
      /\ y2' = 1
      /\ y3' = 1
      /\ pc' = "l1"
      /\ z' = z

l1 == /\ pc = "l1"
      /\ IF y2 \leq x
            THEN /\ pc' = "l2"
            ELSE /\ pc' = "l4"
      /\ UNCHANGED << y1, y2, y3, z >>

l2 == /\ pc = "l2"
      /\ y1' = y1+1
      /\ y2' = y2+y3+2
      /\ y3' = y3+2
      /\ pc' = "l3"
      /\ z' = z

l3 == /\ pc = "l3"
      /\ TRUE
      /\ pc' = "l1"
      /\ UNCHANGED << y1, y2, y3, z >>

l4 == /\ pc = "l4"
      /\ z' = y1
      /\ pc' = "l5"
      /\ UNCHANGED << y1, y2, y3 >>

l5 == /\ pc = "l5"
      /\ PrintT(<<x,z,y1,y2,y3>>)
      /\ pc' = "Done"
      /\ UNCHANGED << y1, y2, y3, z >>

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

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

=========
