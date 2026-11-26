----------------------------- MODULE pluscalappaspd4 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS N,P
ASSUME N % P = 0 /\ P \leq N
(*
--algorithm algo { 
variable
	canal = <<>>;
	witness = -1;
	result = -1;

\*  Macro for sending primitive: sending a message m on the fifo channel chan  
macro Send(m, chan) {
    chan := Append(chan, m);
  };

\*  Macro for receiving  primitive: receiving  a message m on the fifo channel chan  
macro Recv(v, chan) {
    await chan # <<>>; 
    v := Head(chan);
    chan := Tail(chan);
  };

process (one = 1)
variable 
	 x = 0;
	   

{

	w:while (x <= N) {
      a:x := x + 1;
      b:if ( x % P = 0) {
       	   c: Send(x,canal);
       };
};
d: Send(-1,canal);
};

process (two = 2)
variable s = 0,mes;
{
	  w:while (TRUE) {
	  a: if (canal # <<>>) {
	     b:Recv(mes,canal);
		c:if (mes # -1) { d: s := s +mes;}
	  	else {e: goto f;};
	  };
	  };
	  f: print <<s>>;
	  g: result := s; 
      
};



process (three = 3)
variable 
	 i = 0;
	 s = 0;
	 b = N \div P;
{
	w:while ( i< b) {
     
	b: s := s +i;
	a: i := i+1;

	


	
       };
       c:witness := P*s;
    
};
};



}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "63d055f4" /\ chksum(tla) = "3d47ffd7")
\* Label w of process one at line 31 col 11 changed to w_
\* Label a of process one at line 32 col 9 changed to a_
\* Label b of process one at line 33 col 9 changed to b_
\* Label c of process one at line 14 col 5 changed to c_
\* Label d of process one at line 14 col 5 changed to d_
\* Label w of process two at line 43 col 13 changed to w_t
\* Label a of process two at line 44 col 14 changed to a_t
\* Label b of process two at line 19 col 5 changed to b_t
\* Label c of process two at line 46 col 19 changed to c_t
\* Label b of process three at line 65 col 12 changed to b_th
\* Process variable s of process two at line 41 col 10 changed to s_
CONSTANT defaultInitValue
VARIABLES canal, witness, result, pc, x, s_, mes, i, s, b

vars == << canal, witness, result, pc, x, s_, mes, i, s, b >>

ProcSet == {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ canal = <<>>
        /\ witness = -1
        /\ result = -1
        (* Process one *)
        /\ x = 0
        (* Process two *)
        /\ s_ = 0
        /\ mes = defaultInitValue
        (* Process three *)
        /\ i = 0
        /\ s = 0
        /\ b = N \div P
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "w_"
                                        [] self = 2 -> "w_t"
                                        [] self = 3 -> "w"]

w_ == /\ pc[1] = "w_"
      /\ IF x <= N
            THEN /\ pc' = [pc EXCEPT ![1] = "a_"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "d_"]
      /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

a_ == /\ pc[1] = "a_"
      /\ x' = x + 1
      /\ pc' = [pc EXCEPT ![1] = "b_"]
      /\ UNCHANGED << canal, witness, result, s_, mes, i, s, b >>

b_ == /\ pc[1] = "b_"
      /\ IF x % P = 0
            THEN /\ pc' = [pc EXCEPT ![1] = "c_"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "w_"]
      /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

c_ == /\ pc[1] = "c_"
      /\ canal' = Append(canal, x)
      /\ pc' = [pc EXCEPT ![1] = "w_"]
      /\ UNCHANGED << witness, result, x, s_, mes, i, s, b >>

d_ == /\ pc[1] = "d_"
      /\ canal' = Append(canal, (-1))
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << witness, result, x, s_, mes, i, s, b >>

one == w_ \/ a_ \/ b_ \/ c_ \/ d_

w_t == /\ pc[2] = "w_t"
       /\ pc' = [pc EXCEPT ![2] = "a_t"]
       /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

a_t == /\ pc[2] = "a_t"
       /\ IF canal # <<>>
             THEN /\ pc' = [pc EXCEPT ![2] = "b_t"]
             ELSE /\ pc' = [pc EXCEPT ![2] = "w_t"]
       /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

b_t == /\ pc[2] = "b_t"
       /\ canal # <<>>
       /\ mes' = Head(canal)
       /\ canal' = Tail(canal)
       /\ pc' = [pc EXCEPT ![2] = "c_t"]
       /\ UNCHANGED << witness, result, x, s_, i, s, b >>

c_t == /\ pc[2] = "c_t"
       /\ IF mes # -1
             THEN /\ pc' = [pc EXCEPT ![2] = "d"]
             ELSE /\ pc' = [pc EXCEPT ![2] = "e"]
       /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

d == /\ pc[2] = "d"
     /\ s_' = s_ +mes
     /\ pc' = [pc EXCEPT ![2] = "w_t"]
     /\ UNCHANGED << canal, witness, result, x, mes, i, s, b >>

e == /\ pc[2] = "e"
     /\ pc' = [pc EXCEPT ![2] = "f"]
     /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

f == /\ pc[2] = "f"
     /\ PrintT(<<s_>>)
     /\ pc' = [pc EXCEPT ![2] = "g"]
     /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

g == /\ pc[2] = "g"
     /\ result' = s_
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << canal, witness, x, s_, mes, i, s, b >>

two == w_t \/ a_t \/ b_t \/ c_t \/ d \/ e \/ f \/ g

w == /\ pc[3] = "w"
     /\ IF i< b
           THEN /\ pc' = [pc EXCEPT ![3] = "b_th"]
           ELSE /\ pc' = [pc EXCEPT ![3] = "c"]
     /\ UNCHANGED << canal, witness, result, x, s_, mes, i, s, b >>

b_th == /\ pc[3] = "b_th"
        /\ s' = s +i
        /\ pc' = [pc EXCEPT ![3] = "a"]
        /\ UNCHANGED << canal, witness, result, x, s_, mes, i, b >>

a == /\ pc[3] = "a"
     /\ i' = i+1
     /\ pc' = [pc EXCEPT ![3] = "w"]
     /\ UNCHANGED << canal, witness, result, x, s_, mes, s, b >>

c == /\ pc[3] = "c"
     /\ witness' = P*s
     /\ pc' = [pc EXCEPT ![3] = "Done"]
     /\ UNCHANGED << canal, result, x, s_, mes, i, s, b >>

three == w \/ b_th \/ a \/ c

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two \/ three
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Safe ==  pc[3] = "Done" /\ pc[1] ="Done" /\ pc[2] = "Done" => result = witness

prop == Safe
====
