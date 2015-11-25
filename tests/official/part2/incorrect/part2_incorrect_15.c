// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
  int i;
  int j;
  i=0;
  j=0;

  int n;
  assume(n >= 10000);
  assume(n <= 100000);

  while(i < n)
    invariant (j == 2*i),
    invariant (j <= n*2),
    invariant (i <= n)
  {
    i = i + 1;
    j = j + 2;
  }
  
  assert(j == n); // should be n*2
  
  return 0;
}

