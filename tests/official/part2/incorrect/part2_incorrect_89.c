// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;
int z;

int theproc() {
  assume x >= -2147483647;

  int c; 
  c = 0;
  assume x == 0;
  while(x != 0)
    invariant c <= (\old(x) < 0 ? -\old(x) : \old(x)),
      invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      invariant c == \old(x) - \old(y) {
    if(x > 0) {
      x = -x + 1;
    } else {
      x = -x - 1;
    }
    y = y + 1;
    c = c + 1;
  }
  assert x == 0;
  assert c == y - \old(y);
  return 0;
}
