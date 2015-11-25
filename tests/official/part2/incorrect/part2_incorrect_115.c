// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int foo(int x)
  candidate_requires(x >= 0 && x < 10),
  candidate_requires(x < 1),
  candidate_requires(x < 2),
  candidate_requires(x < 3),
  candidate_requires(x < 4),
  candidate_requires(x < 5),
  candidate_requires(x < 6),
  candidate_requires(x < 7),
  candidate_requires(x < 8),
  candidate_requires(x < 9)
{
  if (x < 0 || x >= 10) {
    assert 0;
  }
  return 0;
}

int bar(int x)
  candidate_requires(x >= 0 && x < 10),
  candidate_requires(x < 1),
  candidate_requires(x < 2),
  candidate_requires(x < 3),
  candidate_requires(x < 4),
  candidate_requires(x < 5),
  candidate_requires(x < 6),
  candidate_requires(x < 7),
  candidate_requires(x < 8),
  candidate_requires(x < 9)
{
  int t;
  t = foo(x);
  return 0;
}

int main()
{
  int x;
  x = 0;
  while(x < 11) {
    int t;
    t = bar(x);
    x = x + 1;
  }
  return 0;
}



