void start(int n, int m)
{
  int i;
  assert(0 < m);
  i = n;

  while (i > 0) {
    if (i < m)
      i=i-1;
    else
      i=i-m;
  }
}
