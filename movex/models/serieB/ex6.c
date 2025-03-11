/*@ requires x0 >= 0;
    assigns \nothing;
    ensures \result == x0+2; 
  @*/

int  exemple(int x0) {
  int x=x0;
  //@ assert x == x0;
  x = x + 2;
//@ assert  x == x0 +2;       
return x;
}

