---------------------- MODULE   appex4_3--------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT MAXINT,u,v 

(*
--algorithm gcdscm {
  variables x1 =u; (* 1st integer *)
            x2 = v;  (* 2nd integer *)
            y1;
            y2;
            y3;
            y4;
            z1,z2;
       
 
{
     print <<x1, x2>>;
    
    y1:=x1;
    y2:=x2;
    y3:=x2;
    y4:=0;
    while (y1 /= y2) {
    
      while  ( y1 > y2) {
        y1:=y1-y2;
        y4:=y4+y3;
      };
      while  ( y2 > y1) {
        y2:=y2-y1;
        y3:=y4+y3;
      };
   
    };
    z1 := y1;
    z2 := y3+y4;
    print <<x1, x2,z1,z2>>
}

}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x1, x2, y1, y2, y3, y4, z1, z2, pc

vars == << x1, x2, y1, y2, y3, y4, z1, z2, pc >>

Init == (* Global variables *)
        /\ x1 = u
        /\ x2 = v
        /\ y1 = defaultInitValue
        /\ y2 = defaultInitValue
        /\ y3 = defaultInitValue
        /\ y4 = defaultInitValue
        /\ z1 = defaultInitValue
        /\ z2 = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(<<x1, x2>>)
         /\ y1' = x1
         /\ y2' = x2
         /\ y3' = x2
         /\ y4' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << x1, x2, z1, z2 >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF y1 /= y2
               THEN /\ pc' = "Lbl_3"
                    /\ UNCHANGED << z1, z2 >>
               ELSE /\ z1' = y1
                    /\ z2' = y3+y4
                    /\ PrintT(<<x1, x2,z1',z2'>>)
                    /\ pc' = "Done"
         /\ UNCHANGED << x1, x2, y1, y2, y3, y4 >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF y1 > y2
               THEN /\ y1' = y1-y2
                    /\ y4' = y4+y3
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Lbl_4"
                    /\ UNCHANGED << y1, y4 >>
         /\ UNCHANGED << x1, x2, y2, y3, z1, z2 >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF y2 > y1
               THEN /\ y2' = y2-y1
                    /\ y3' = y4+y3
                    /\ pc' = "Lbl_4"
               ELSE /\ pc' = "Lbl_2"
                    /\ UNCHANGED << y2, y3 >>
         /\ UNCHANGED << x1, x2, y1, y4, z1, z2 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Q1 == pc # "Done"
(* Qpc == pc ="Done" => z1=gcd(x1,x2) /\ z2=scm(x1,x2) *)
D == 0..MAXINT\cup {defaultInitValue}
Qpc1 == pc = "Done" => ( x1 % z1  = 0 ) /\ (x2 % z1 = 0)
Qpc2 == pc = "Done" => ( z2 % x1  = 0 ) /\ (z2 % x2 = 0)
Qproperty1 == pc = "Done" => x1*x2=z1*z2
Qef == x1 \in D /\ x2 \in D /\ y1 \in D /\ y3 \in D /\ z1 \in D /\ z2 \in D 

==================================================================
\* Modification History
\* Last modified Thu Nov 19 20:42:02 CET 2020 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
