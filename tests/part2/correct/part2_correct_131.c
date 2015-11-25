// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{

  int i;

  i = 100;

  while(i < 200)
    candidate_invariant (i >= 100),
    candidate_invariant (i > 0),
    candidate_invariant (i <= 200),
    candidate_invariant (i == 0),
    candidate_invariant (i == i + 1),
    candidate_invariant (0)
  {
    i = i + 1;
    assert(i > 0);
  }
  assert(i == 200);

  return 0;
}

