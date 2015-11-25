// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int x;
int y;
int z;

int theproc() requires x + y == z, ensures \result == 52
{
  int a;
  a = 1;
  while(a < (1 << 24))
       invariant a <= (1 << 24),
	 invariant (a&(a-1)) == 0,
       invariant a > 0 {
    int b;
    int c;
    b = 1;
    c = a;
    while(c > 0) invariant c == 0 || b*c == a,
                   invariant b >= 1,
                   invariant b <= 2*a,
		   invariant (b&(b-1)) == 0,
			      invariant (c&(c-1)) == 0 {
      assert b*c == a;
      b = b << 1;
      c = c >> 1;
    }
    a = a << 1;
  }
  assert a == (1 << 24);
  return 52;
}

