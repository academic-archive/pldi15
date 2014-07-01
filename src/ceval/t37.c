void count_down(int x) {
  if (x>0) {
    x--;
    count_down(x);
  }
}

int copy(int x, int y) {
  if (x>0) {
    y++;
    x--;
    y=copy(x, y);
  }
  return y;
}

void main(int x, int y) {
  y = copy(x, y);
  count_down(y);
}
