int nondet(void);

void main(int n)
{
  int x=0;

  while (x<n) {
    if (nondet())
      x=x+1;
    else 
      x=x+1;
  }
}
