// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int x;
int y;
int z;

int theproc() requires x + y != z, ensures \result == 52 {
  while(x > 0) invariant x + y != z {
    x = x - 1;
    y = y + 1;
  }
  assert x + y != z;
  return 52;
}
