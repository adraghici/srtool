// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int main()
{

  int i;

  i = 102;

  while(i >= 100)
  candidate_invariant ((i%2) == 0)
  {
    i = i - 2;
    assert(i > 0);
  }
  assert(i > 100);

  return 0;
}
