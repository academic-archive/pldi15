void start(int x, int y, int n, int m)
{
  while (n>x) {
    if (m>y)
      y = y+1;
    else
      x = x+1;
  }
}
