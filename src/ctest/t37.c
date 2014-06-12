
void count_down (x) {
  int a = x;
  if (a>0) {
    a = a-1;
    count_down(a);
  }
}
int copy (x,y) {
  if (x>0) {
    y = y+1;
    x = x-1;
    y=copy(x,y);
  };
  return y;
}
void _main (x,y) {
  y = copy (x,y);
  count_down(y);
}



int main(int argc, char **argv)
{
  int x,y;
}
