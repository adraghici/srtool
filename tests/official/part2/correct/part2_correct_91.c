// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;
int z;


int f()
  candidate_requires x >= 0,
  candidate_requires y >= 0,
  candidate_requires z >= 0,
  candidate_requires x > y,
  candidate_requires x > z,
  candidate_requires y > x,
  candidate_requires y > z,
  candidate_requires z > x,
  candidate_requires z > y,
  candidate_ensures x >= y,
  candidate_ensures x >= z,
  candidate_ensures y >= x,
  candidate_ensures y >= z,
  candidate_ensures z >= x,
  candidate_ensures z >= y,
  candidate_ensures x > y,
  candidate_ensures x > z,
  candidate_ensures y > x,
  candidate_ensures y > z,
  candidate_ensures z > x,
  candidate_ensures z > y,
  candidate_ensures x >= 0,
  candidate_ensures y >= 0,
  candidate_ensures z >= 0
{
  if(x > 0) {
    x = x - 1;
  }
  if (y > 0) {
    y = y - 1;
  }
  return 0;
}


int g() {
  x = 12;
  y = 11;
  z = 13;

  int temp;

  temp = f();
  temp = f();
  temp = f();

  assert z > x;
  assert z > y;

  return 0;
}
