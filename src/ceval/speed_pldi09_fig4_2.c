void start(int n, int m)
{
  int va, vb;
/* assert(n > 0); */
  assert(m > 0);
  va = n;
  vb = 0;

  while (va > 0) {
    if (vb < m) { 
      vb=vb+1; 
      va=va-1;
    } else {
      vb=vb-1;
      vb=0;
    }
  }
}
