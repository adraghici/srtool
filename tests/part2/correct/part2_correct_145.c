// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{

  int i;

  i = 200;

  while(i >= 100)
  //candidate_invariant (i >= 98)
  candidate_invariant ((i%2) == 0 )
  {
    i = i - 2;
    assert(i > 0);
  }
  assert(i == 98);

  return 0;
}

