
void count_up (int,int);
void count_down (int,int);

void count_down (int x,int y)
{ int a = x;
  if (a>y) {
    a = a-1;
    count_up(a,y);
  }
}

void count_up (int x, int y)
{ int a = y;
  if (a+1<x) {
    a = a+2;
    count_down(x,a);
  }
}

void _main (int y, int z) {
  count_down(y,z);
}

int main(int argc, char **argv)
{
  int x,y;
}


