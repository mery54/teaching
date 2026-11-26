----------------------------- MODULE pluscalappaspd4q -------------------
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




===