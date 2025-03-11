int q1()
{
  int x=10;
  int z=2*x;
  int y=z+x;
//@ assert l1:  x== 10 && y == z+x && z==2*x;
 y= z+x;
//@ assert l2: x== 10 && y == x+2*10;
 x = x+1;
//@ assert l3: x-1== 10 && y == x-1+2*10; 
return(0);
}
