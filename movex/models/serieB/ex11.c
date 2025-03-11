/*@ axiomatic  max{
  @ logic integer max(integer n,integer m);
  @ axiom max1: \forall integer n,m; n <= m  
  ==> max(n,m) == m;
  @ axiom max2: \forall integer n,m; n > m  
  ==> max(n,m) == n;
@} */



/*@ requires x0 >= 0 && y0 >=0;
    assigns \nothing;
    ensures \result == max(x0,y0); 
  @*/

int  maximum(int x0,int y0,int z0) {
  int x=x0;
  int y=y0;
  int z=z0;
  //@ assert max(x0,x0) == x0;
  //@ assert max(x0,y0) == max(y0,x0);    
//@ assert x== x0 && y == y0 && z==z0;
if (x < y) {
//@ assert x < y && x== x0 && y == y0 && z==z0;
//@ assert x < y && x== x0 && y == y0 && y==y;    
 z = y;
//@ assert x < y && x== x0 && y == y0 && z==y;  
}
 else
   {
//@ assert x >= y && x== x0 && y == y0 && z==z0;
//@ assert x >= y && x== x0 && y == y0 && x==x;        
     
 z = x;
//@ assert x >= y && x== x0 && y == y0 && z==x;       
   };
//@ assert  x== x0 && y == y0 && z==max(x,y);       
return z;
}


