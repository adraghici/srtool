// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"


int x;
int y;
int z;

int foo()
candidate_requires x && y && z, candidate_requires x && y && !z, candidate_requires x && !y && z, candidate_requires x && !y && !z, candidate_requires !x && y && z, candidate_requires !x && y && !z, candidate_requires !x && !y && z, candidate_requires !x && !y && !z,
  candidate_ensures x && y && z, candidate_ensures x && y && !z, candidate_ensures x && !y && z, candidate_ensures x && !y && !z, candidate_ensures !x && y && z, candidate_ensures !x && y && !z, candidate_ensures !x && !y && z, candidate_ensures !x && !y && !z,
  candidate_ensures \result == 1,
  candidate_ensures \result == 2,
  candidate_ensures \result == 3,
  candidate_ensures \result == 4,
  candidate_ensures \result == 5,
  candidate_ensures \result == 6,
  candidate_ensures \result == 7,
  candidate_ensures \result == 8,
  candidate_ensures \result == 9,
  candidate_ensures \result == 10,
  candidate_ensures \result == 11,
  candidate_ensures \result == 12
{
  int t;
  t = x;
  x = y;
  y = t;
  return 13;
}


int bar()
candidate_requires x && y && z, candidate_requires x && y && !z, candidate_requires x && !y && z, candidate_requires x && !y && !z, candidate_requires !x && y && z, candidate_requires !x && y && !z, candidate_requires !x && !y && z, candidate_requires !x && !y && !z,
  candidate_ensures x && y && z, candidate_ensures x && y && !z, candidate_ensures x && !y && z, candidate_ensures x && !y && !z, candidate_ensures !x && y && z, candidate_ensures !x && y && !z, candidate_ensures !x && !y && z, candidate_ensures !x && !y && !z,
  candidate_ensures \result == 1,
  candidate_ensures \result == 2,
  candidate_ensures \result == 3,
  candidate_ensures \result == 4,
  candidate_ensures \result == 5,
  candidate_ensures \result == 6,
  candidate_ensures \result == 7,
  candidate_ensures \result == 8,
  candidate_ensures \result == 9,
  candidate_ensures \result == 10,
  candidate_ensures \result == 11,
  candidate_ensures \result == 12,
  candidate_ensures \result == 13
{
  int t;
  t = x;
  x = y;
  y = t;
  t = foo();
  return t;
}

int baz()
candidate_requires x && y && z, candidate_requires x && y && !z, candidate_requires x && !y && z, candidate_requires x && !y && !z, candidate_requires !x && y && z, candidate_requires !x && y && !z, candidate_requires !x && !y && z, candidate_requires !x && !y && !z,
  candidate_ensures x && y && z, candidate_ensures x && y && !z, candidate_ensures x && !y && z, candidate_ensures x && !y && !z, candidate_ensures !x && y && z, candidate_ensures !x && y && !z, candidate_ensures !x && !y && z, candidate_ensures !x && !y && !z,
  candidate_ensures \result == 1,
  candidate_ensures \result == 2,
  candidate_ensures \result == 3,
  candidate_ensures \result == 4,
  candidate_ensures \result == 5,
  candidate_ensures \result == 6,
  candidate_ensures \result == 7,
  candidate_ensures \result == 8,
  candidate_ensures \result == 9,
  candidate_ensures \result == 10,
  candidate_ensures \result == 11,
  candidate_ensures \result == 12,
  candidate_ensures \result == 13
{
  int t;
  t = x;
  x = y;
  y = t;
  t = bar();
  return t;
}

int qiz()
candidate_requires x && y && z, candidate_requires x && y && !z, candidate_requires x && !y && z, candidate_requires x && !y && !z, candidate_requires !x && y && z, candidate_requires !x && y && !z, candidate_requires !x && !y && z, candidate_requires !x && !y && !z,
  candidate_ensures x && y && z, candidate_ensures x && y && !z, candidate_ensures x && !y && z, candidate_ensures x && !y && !z, candidate_ensures !x && y && z, candidate_ensures !x && y && !z, candidate_ensures !x && !y && z, candidate_ensures !x && !y && !z,
  candidate_ensures \result == 1,
  candidate_ensures \result == 2,
  candidate_ensures \result == 3,
  candidate_ensures \result == 4,
  candidate_ensures \result == 5,
  candidate_ensures \result == 6,
  candidate_ensures \result == 7,
  candidate_ensures \result == 8,
  candidate_ensures \result == 9,
  candidate_ensures \result == 10,
  candidate_ensures \result == 11,
  candidate_ensures \result == 12,
  candidate_ensures \result == 13
{
  int t;
  t = x;
  x = y;
  y = t;
  t = baz();
  return t;
}

int main() ensures \result == 13
{
  assume x ? y : z;
  int t;
  t = qiz();
  return t;
}


