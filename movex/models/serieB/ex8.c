
/*@
  requires a + b == 6;
  ensures \result == 4;

*/

int annotation(int a,int b)
{
  int x,y,z;
  //@ assert   a == a &&  a == a && b == b &&  a == a && b == b &&  a + b -2 ==4;           
  
  x = a;
  //@ assert   x == a &&  x == a && b == b &&  x == a && b == b &&  a + b -2 ==4;           
  y = b;
  //@ assert  x == a && y == b &&  x == a && y == b &&  a + b -2 ==4;          
  z = a+b-2;
  /*@ assert x == a && y == b && z==4; */        
  return(z);
  }
