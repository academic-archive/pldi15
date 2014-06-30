int gcd(int x, int y) {
  if (x <= 0) return y;
  if (y <= 0) return x;
  for (;;) {
         if (x>y) x -= y;
    else if (y>x) y -= x;
    else return x;
  }
}
