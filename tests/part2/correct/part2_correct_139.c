// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{

  int i;
  int j;
  int k;
  int l;

  i = j;

  while(i < 100)
    candidate_invariant (i != j),
    candidate_invariant ((i - j) == 0),
    candidate_invariant ((i + j) > 0),
    candidate_invariant ((i == i + i + j - j - i))
  {
    i = i + 1;
    j = j + 1;
    k = 0;
    l = 0;
    while(k < 200)
      candidate_invariant (k != l),
      candidate_invariant (k == l),
      candidate_invariant (i == k),
      candidate_invariant (j == k)
    {
      k = k + 1;
      l = l + 1;
    }
    i = i + k;
    j = j + l;
  }
  assert(i == j);

  return 0;
}

