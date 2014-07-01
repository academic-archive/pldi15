int nondet(void);

void main(int n)
{
  while (n>0) {
    n=n-1;
    while (n>0) {
      if (nondet()) break;
      n=n-1;
    }
  }
}
