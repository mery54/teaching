--------- MODULE appex5_6 --------
EXTENDS Integers,TLC
CONSTANTS x0  (* x is the input *), 
          UND (* undefined value *)
    
  
--------------------------------------------------------------
MAX == 32767  (* 16 bits *)
D == 0..MAX
y10 == UND (* y10  initial value of y1 is UNDefined *)
y20 == UND  (* y10  initial value of y1 is UNDefined *) 
y30 == UND  (* y10  initial value of y1 is UNDefined *) 
z0 == UND   (* y10  initial value of y1 is UNDefined *)

--------------------------------------------------------------
(*  we assume that x0 \leq MAX *)
DD(X) ==  ( X # UND =>  X \in D)
init(X) ==  ( X # UND)
requires  == 
    /\ x0 \geq 0
    /\ y10 \in Int
    /\ y20 \in Int 
    /\ y30 \in Int
    /\ z0 \in Int
--------------------------------------------------------------
ASSUME requires
--------------------------------------------------------------

(*
--algorithm  squareroot {
variables y1=y10,y2=y20,y3=y30,z=z0,x=x0;
{
l0: assert  x>= 0 /\ y1 \in Int /\ y2 \in Int /\ y3 \in Int /\ z \in Int;
y1:=0;y2:=1;y3:=1;
l1: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x;
w: while (y2 \leq x){
    l2: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y2  \leq x;
    y1:=y1+1;
    y2:=y2+y3+2; y3:=y3+2;
    l3: assert y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x; 
    };
l4: z:=y1;
l5: print <<x,z,y1,y2,y3>>;
    }
 }

*)
\* BEGIN TRANSLATION (chksum(pcal) = "2b855e57" /\ chksum(tla) = "6b997366")
VARIABLES y1, y2, y3, z, x, pc

vars == << y1, y2, y3, z, x, pc >>

Init == (* Global variables *)
        /\ y1 = y10
        /\ y2 = y20
        /\ y3 = y30
        /\ z = z0
        /\ x = x0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x>= 0 /\ y1 \in Int /\ y2 \in Int /\ y3 \in Int /\ z \in Int, 
                "Failure of assertion at line 33, column 5.")
      /\ y1' = 0
      /\ y2' = 1
      /\ y3' = 1
      /\ pc' = "l1"
      /\ UNCHANGED << z, x >>

l1 == /\ pc = "l1"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x, 
                "Failure of assertion at line 35, column 5.")
      /\ pc' = "w"
      /\ UNCHANGED << y1, y2, y3, z, x >>

w == /\ pc = "w"
     /\ IF y2 \leq x
           THEN /\ pc' = "l2"
           ELSE /\ pc' = "l4"
     /\ UNCHANGED << y1, y2, y3, z, x >>

l2 == /\ pc = "l2"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y2  \leq x, 
                "Failure of assertion at line 37, column 9.")
      /\ y1' = y1+1
      /\ y2' = y2+y3+2
      /\ y3' = y3+2
      /\ pc' = "l3"
      /\ UNCHANGED << z, x >>

l3 == /\ pc = "l3"
      /\ Assert(y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x, 
                "Failure of assertion at line 40, column 9.")
      /\ pc' = "w"
      /\ UNCHANGED << y1, y2, y3, z, x >>

l4 == /\ pc = "l4"
      /\ z' = y1
      /\ pc' = "l5"
      /\ UNCHANGED << y1, y2, y3, x >>

l5 == /\ pc = "l5"
      /\ PrintT(<<x,z,y1,y2,y3>>)
      /\ pc' = "Done"
      /\ UNCHANGED << y1, y2, y3, z, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ w \/ l2 \/ l3 \/ l4 \/ l5
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


Safety_absence ==  DD(y1)  /\ DD(y2) /\ DD(y3) /\ DD(z)

Safety_partialcorrectness == pc="Done" =>  z*z\leq x /\ x < (z+1)*(z+1)

Inv == 
    /\ pc \in {"l0","l1","l2","l3","l4","Done","l5","l33","w"}
    /\  (init(y1) /\ init(y2) /\ init(y3) /\ init(z)) => (y1 \in Nat /\ y2 \in Nat /\ y3 \in Nat /\ z \in Nat)
    /\ pc = "l0" =>  (y1 = UND /\ y2 = UND /\ y3 = UND /\ z = UND)
    /\ pc = "l1"  => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x
    /\ pc = "l2" => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y2  \leq x
    /\ pc="l3" => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x
    /\ pc="l4" => y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x /\ x < y2
    /\ pc="l5" => z=y1 /\ y2 = (y1+1)*(y1+1) /\ y3 = 2*y1+1 /\ y1*y1  \leq x /\ x < y2    
    /\ Safety_partialcorrectness 

Box == []Inv
check ==  
    /\ Safety_absence
    /\ Safety_partialcorrectness
    /\ Inv

=========
