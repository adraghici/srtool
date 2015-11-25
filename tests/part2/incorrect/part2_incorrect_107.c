// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;

int foo() ensures \result == 1 {
  return 1;
}

int reallydonttouchx() {
  int a;
  a = 0;
  while(a < 10) {
    int temp;
    x = foo();
    a = a + 1;
  }
  return 0;
}

int donttouchx()
{
  int t;
  t = reallydonttouchx();
  return 0;
}

int cadge()
  requires x == y,
  ensures x == y,
  ensures x == \old(x),
  ensures y == \old(y)
{
  int t;
  t = donttouchx();
  return t;
}

