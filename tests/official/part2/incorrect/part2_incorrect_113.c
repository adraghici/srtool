// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int y;
int x;

int marge()
  requires x == 0 || x == 1,
  requires y == 0 || y == 1,
  requires x == 1 - y,
  ensures x + y == 1
{
  x = 1 - \old(y);
  y = 1 - \old(y);
  int t;
  t = badge();
  return 0;
}

int badge()
  requires x == 0 || x == 1,
  requires y == 0 || y == 1,
  requires x == 1 - y,
  ensures x + y == 1
{
  x = 1 - \old(y);
  y = 1 - \old(x);
  int t;
  t = zadge();
  return 0;
}

int zadge()
  requires x == 0 || x == 1,
  requires y == 0 || y == 1,
  requires x == 1 - y,
  ensures x + y == 1
{
  x = 1 - \old(y);
  y = 1 - \old(x);
  int t;
  t = cadge();
  return 0;
}

int cadge()
  requires x == 0 || x == 1,
  requires y == 0 || y == 1,
  requires x == 1 - y,
  ensures x + y == 1
{
  x = 1 - \old(y);
  y = 1 - \old(x);
  int t;
  t = marge();
  return 0;
}



