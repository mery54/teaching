----------------------------- MODULE pluscalil261 -------------------
EXTENDS Integers,Naturals,Sequences,TLC
CONSTANTS
	N,K




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
	i:if (N=2*K) {
       witness := (K+1)*(K+1);
       }
       else {
       witness := (K)*(K);
	};
 };

}
end algorithm;


*)

(*  mistake in the test N=2*K which should be N # 2*K *)

========================
