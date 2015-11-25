// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
  int i;
  int n;
  i = 3;
  assume(n >= 10000);
  assume(n <= 20000);
  
  int origN; 
  origN = n;

  while (n > 0)
    invariant (i >= 3),
    invariant ( i == (origN - n) + 3 )
  {
    i = i + 1;
    n = n - 1;
  }
  assert(i >= 3);
  return 0;
}
