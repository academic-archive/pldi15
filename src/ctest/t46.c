int x,y;

void _tick (int x) {}

void produce () {
  while (x>0) {
    _tick(-1); x=x-1; y=y+1;
  }
}
void consume () {
  while (y>0) {
    y=y-1; x=x+1; _tick(1);
  }
}
void _main (int y, int z) {
  consume(); produce(); consume();
}


int main(int argc, char **argv)
{
  int x,y;
}


