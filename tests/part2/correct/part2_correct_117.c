// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc(int a) requires a < 10 {

  int t;
  t = a;

  int r;
  r = 5;

  while(t >= 0) {
    int v;
    havoc v;
    if(v) {
      r = t;
    }
    assume v < t;
    t = v;
  }
  assert r < 10;
  return 0;
}
