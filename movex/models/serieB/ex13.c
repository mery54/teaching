int reste(int a, int b) {
  int r = a;
  int q = 0; 
  while (r >= b) {
    r = r - b;
    q = q +1;
  };
  return r;
}
