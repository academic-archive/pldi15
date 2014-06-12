
int main(int argc, char **argv)
{
  int i,j,n;

  i=0;
  while (i<n) {
    j=i;
    j=j+1;
  }
  while (j<n) {
    if (0) {
      _tick(1);
      j=j-1;
      n=n-1;
    }
    j=j+1;
  }
  i=i+1;
}
