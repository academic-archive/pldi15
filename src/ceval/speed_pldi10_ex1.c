int nondet(void);

void start(int n)
{
  int i,j;

  i=0;
  while (i<n) {
    j=i+1;
    while (j<n) {
      if (nondet()) {
        tick(1);
        j=j-1;
        n=n-1;
      }
      j=j+1;
    }
    i=i+1;
  }
}
