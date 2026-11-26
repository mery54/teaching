----------------------------- MODULE pluscalil261 -------------------
EXTENDS Integers,Naturals,Sequences,TLC
CONSTANTS
	N,K
ASSUME (N = 2*K+1) \/ (N=2*K)



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
	w:while (x < N) {
      a:x := x + 1;
      b:if ( x % 2 # 0) {
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
{
	i:if (N#2*K) {
       witness := (K+1)*(K+1);
       }
       else {
       witness := (K)*(K);
	};
 };

}
end algorithm;


*)
\* BEGIN TRANSLATION (chksum(pcal) = "cef05887" /\ chksum(tla) = "f2a8dd4b")
\* Label w of process one at line 31 col 11 changed to w_
\* Label a of process one at line 32 col 9 changed to a_
\* Label b of process one at line 33 col 9 changed to b_
\* Label c of process one at line 17 col 5 changed to c_
\* Label d of process one at line 17 col 5 changed to d_
CONSTANT defaultInitValue
VARIABLES canal, witness, result, pc, x, s, mes

vars == << canal, witness, result, pc, x, s, mes >>

ProcSet == {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ canal = <<>>
        /\ witness = -1
        /\ result = -1
        (* Process one *)
        /\ x = 0
        (* Process two *)
        /\ s = 0
        /\ mes = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "w_"
                                        [] self = 2 -> "w"
                                        [] self = 3 -> "i"]

w_ == /\ pc[1] = "w_"
      /\ IF x < N
            THEN /\ pc' = [pc EXCEPT ![1] = "a_"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "d_"]
      /\ UNCHANGED << canal, witness, result, x, s, mes >>

a_ == /\ pc[1] = "a_"
      /\ x' = x + 1
      /\ pc' = [pc EXCEPT ![1] = "b_"]
      /\ UNCHANGED << canal, witness, result, s, mes >>

b_ == /\ pc[1] = "b_"
      /\ IF x % 2 # 0
            THEN /\ pc' = [pc EXCEPT ![1] = "c_"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "w_"]
      /\ UNCHANGED << canal, witness, result, x, s, mes >>

c_ == /\ pc[1] = "c_"
      /\ canal' = Append(canal, x)
      /\ pc' = [pc EXCEPT ![1] = "w_"]
      /\ UNCHANGED << witness, result, x, s, mes >>

d_ == /\ pc[1] = "d_"
      /\ canal' = Append(canal, (-1))
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << witness, result, x, s, mes >>

one == w_ \/ a_ \/ b_ \/ c_ \/ d_

w == /\ pc[2] = "w"
     /\ pc' = [pc EXCEPT ![2] = "a"]
     /\ UNCHANGED << canal, witness, result, x, s, mes >>

a == /\ pc[2] = "a"
     /\ IF canal # <<>>
           THEN /\ pc' = [pc EXCEPT ![2] = "b"]
           ELSE /\ pc' = [pc EXCEPT ![2] = "w"]
     /\ UNCHANGED << canal, witness, result, x, s, mes >>

b == /\ pc[2] = "b"
     /\ canal # <<>>
     /\ mes' = Head(canal)
     /\ canal' = Tail(canal)
     /\ pc' = [pc EXCEPT ![2] = "c"]
     /\ UNCHANGED << witness, result, x, s >>

c == /\ pc[2] = "c"
     /\ IF mes # -1
           THEN /\ pc' = [pc EXCEPT ![2] = "d"]
           ELSE /\ pc' = [pc EXCEPT ![2] = "e"]
     /\ UNCHANGED << canal, witness, result, x, s, mes >>

d == /\ pc[2] = "d"
     /\ s' = s +mes
     /\ pc' = [pc EXCEPT ![2] = "w"]
     /\ UNCHANGED << canal, witness, result, x, mes >>

e == /\ pc[2] = "e"
     /\ pc' = [pc EXCEPT ![2] = "f"]
     /\ UNCHANGED << canal, witness, result, x, s, mes >>

f == /\ pc[2] = "f"
     /\ PrintT(<<s>>)
     /\ pc' = [pc EXCEPT ![2] = "g"]
     /\ UNCHANGED << canal, witness, result, x, s, mes >>

g == /\ pc[2] = "g"
     /\ result' = s
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << canal, witness, x, s, mes >>

two == w \/ a \/ b \/ c \/ d \/ e \/ f \/ g

i == /\ pc[3] = "i"
     /\ IF N#2*K
           THEN /\ witness' = (K+1)*(K+1)
           ELSE /\ witness' = (K)*(K)
     /\ pc' = [pc EXCEPT ![3] = "Done"]
     /\ UNCHANGED << canal, result, x, s, mes >>

three == i

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two \/ three
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") => (result=witness)
Safe2 ==   (\E self \in ProcSet: pc[self] # "Done")
Safe == Safe1
========================
