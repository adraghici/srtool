// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{

  int i;
  int j;

  i = j;

  while(i < 100)
    candidate_invariant (i != j),
    candidate_invariant ((i - j) == 0),
    candidate_invariant ((i + j) > 0),
    candidate_invariant ((i == i + i + j - j - i))
  {
    i = i + 1;
    j = j + 1;
  }
  assert(i == j);

  return 0;
}

