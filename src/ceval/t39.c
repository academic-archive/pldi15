void count_up(int, int);

void count_down(int x,int y)
{
  if (x>y) {
    x--;
    count_up(x, y);
  }
}

void count_up(int x, int y)
{
  if (y+1<x) {
    y += 2;
    count_down(x, y);
  }
}

void start(int y, int z) {
  count_down(y, z);
}
