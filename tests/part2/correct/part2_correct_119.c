// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int x; int y; int z; int w;

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
