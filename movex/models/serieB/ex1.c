int q1()
{
  // ==>
    //@ assert  10== 10 && 2*10+10  == 2*10+10 && 2*10==2*10;    
  int x=10;
  //@ assert  x== 10 && 2*x+x  == 2*x+x && 2*x==2*x;    
  int z=2*x;
  //@ assert  x== 10 && z+x  == z+x && z==2*x;  
  int y=z+x;
  //@ assert  x== 10 && y == z+x && z==2*x;
  // ==>
  //@ assert  x== 10 && z+x  == x+2*10;  
  y= z+x;
  //@ assert  x== 10 && y == x+2*10;
  // ==> 
  //@ assert  x+1-1== 10 && y == x+1-1+2*10;   
  x = x+1;
  //@ assert  x-1== 10 && y == x-1+2*10; 
  return(0);
}
