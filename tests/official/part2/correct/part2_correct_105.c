// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc() {

  int x;
  x = 0;
  while(x < 99) invariant x <= 100, invariant (x % 2) == 0 {
      int t;
      t = x;
      havoc x;
      assume x == t + 2;
    }
  assert x == 100;
  return 0;
}
