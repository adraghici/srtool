// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

// computes a triangular number

int main()
{
  int n;
  assume(0 <= n);
  assume(n <= 10000);
  int i;
  int j;
  i = 0; j = 0;
  while (i < n)
    candidate_invariant (2*j == i*(i-1))
  {
    j = j + i;
    i = i + 1;
  }
  assert(2*j == n*(n-1));
  return 0;
}
