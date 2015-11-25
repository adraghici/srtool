// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{

  int i;

  i = 200;

  while(i >= 100)
    candidate_invariant (i >= 100),
    candidate_invariant (i > 0),
    candidate_invariant (i >= 98),
    candidate_invariant ((i % 2) == 0),
    candidate_invariant ((i % 2) == 1),
    candidate_invariant (i == 17)
  {
    i = i - 2;
    assert(i > 0);
  }
  assert(i > 0);

  return 0;
}
