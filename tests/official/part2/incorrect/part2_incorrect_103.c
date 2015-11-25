// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x; int y; int z; int w;

// spec is not strong enough
int theproc()
  requires x != y,
  requires x != z,
  requires x != w,
  requires y != z,
  requires y != w,
  requires z != w,
  ensures \result == w {
  while(x != w) {
    x = y;
    y = z;
    z = w;
  }
  return x;
}

int theotherproc() ensures \result == 0 {
  int a;
  a = 5;
  while(a) {
    x = a;
    y = a + 1;
    z = a + 2;
    w = a + 3;
    int t;
    t = theproc();
    if(x == a + 3) {
      a = a - 1;
    } else {
      assert 0;
    }    
  }
  return a;
}
