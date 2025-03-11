int main()
{
//@ assert  37 == 37;  
  int a = 42;
//@ assert  37 == 37;  
  int b = 37;
//@ assert  b == 37;  
  int c = a+b;
//@ assert  b == 37;
  // ==>
//@ assert  b+a-c == 0 && c == 79;
  a = a -  c;
//@ assert  b+a == 0 && c == 79;
  b=  b +  a; 
//@ assert  b == 0 && c == 79;
  return(0);
}
