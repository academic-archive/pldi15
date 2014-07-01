/* Quicksort */

int nondet();

void qsort(int *a, int lo, int hi) {
  int m1, m2, n;

  if (hi - lo < 1)
    return;

  n = nondet();   /* partition the array */
  assert( n > 0 );
  assert( lo + n <= hi );

  m1 = n + lo;
  m2 = m1 - 1;

  qsort(a, m1, hi);
  qsort(a, lo, m2);
}

void start(int *a, int len) {
  qsort(a, 0, len);
}
