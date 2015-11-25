// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
  int i; int j; int k;
  i=0; j=1; k=2;

  int n;
  assume(n >= 10000);
  assume(n <= 100000);
  assume((n%4)==0);

  while(i < n)
    candidate_invariant ((i % 2) == 0),
    candidate_invariant ((j % 2) == 1),
    candidate_invariant ((k % 2) == 0)
  {
    i = i + k;
    j = j + k;
    k = i + k;
  }

  assert((i % 2) == 0);
  return 0;
}
