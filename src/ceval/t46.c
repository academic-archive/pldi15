int x, y;

void produce() {
  while (x > 0) {
    tick(-1); x--; y++;
  }
}

void consume() {
  while (y > 0) {
    y--; x++; tick(1);
  }
}

void main(int y, int z) {
  consume(); produce(); consume();
}
