// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int x;
int y;

int foo()
  candidate_requires(x >= 0 && x < 10),
  candidate_requires(x >= 0 && x <= 10),
  candidate_requires x == y,
  candidate_ensures x == y,
  candidate_ensures x == \old(x) + 1
{
  if (x != y) {
    assert 0;
  }
  x = x + 1;
  y = y + 1;
  return 0;
  }

int bar()
  candidate_requires x == y,
  candidate_ensures x == y,
  candidate_ensures x == \old(x) + 1,
  candidate_requires(x >= 0 && x < 10),
  candidate_ensures(x >= 0 && x <= 10),
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
  t = foo();
  return 0;
}

int main()
{
  assume x >= y;
  assume !(x > y);
  assume x > 0;
  while(x < 10) {
    int t;
    t = bar();
    assert x <= 10;
    x = x + 1;
    y = y + 1;
  }
  return 0;
}



