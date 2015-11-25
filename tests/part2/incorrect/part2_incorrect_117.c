// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;

int donttouchx()
{
  havoc x;
  return 0;
}

int cadge()
  requires x > y,
  ensures x > y,
  ensures x == \old(x),
  ensures y == \old(y)
{
  int t;
  t = donttouchx();
  return t;
}

