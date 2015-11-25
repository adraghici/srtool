// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc(int a) requires (a & (a-1)) == 0, requires a >= 0, ensures \result == a {

  int d;
  d = a;
  while(d > 0) invariant (d & (d-1)) == 0, invariant d >= 0 {
      if(d > 1) {
	assert (d/2)*2 == d;
      }
      d = d >> 1;
    }
  assert d == 0;
  return d + a;
}
