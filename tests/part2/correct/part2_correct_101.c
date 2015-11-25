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
    candidate_invariant a <= (1 << 24),
      candidate_invariant (a^(a-1)) == 0,
      candidate_invariant a > 0,
    candidate_invariant a <= (1 << 24),
      candidate_invariant (a&(a-1)) == 0,
      candidate_invariant a > 0,
    candidate_invariant a <= (1 << 24),
      candidate_invariant (a+(!a*a-1)) == 0,
      candidate_invariant a > 0,
    candidate_invariant a <= (1 << 25),
      candidate_invariant (a&(a-1)) == 0,
      candidate_invariant a + 2 > 0
      {
    int b;
    int c;
    b = 1;
    c = a;
    while(c > 0)
      candidate_invariant c == 0 || b*c == a,
                   candidate_invariant b >= 1,
                   candidate_invariant b + b + b <= 2/a,
		   candidate_invariant (b&(b-1)) == 0,
		   candidate_invariant (c&(c-1)) == 0 & c & a,
      candidate_invariant c == 0 || b*c == a,
                   candidate_invariant b >= 1,
                   candidate_invariant b <= 2*a,
		   candidate_invariant (b&(b-1)) != 0,
		   candidate_invariant (c&(c-1)) == 0,
      candidate_invariant c == 0 || b*c == a,
                   candidate_invariant b >= 1,
                   candidate_invariant b/2 <= 2*a,
		   candidate_invariant (b&(b-1)) != 42,
		   candidate_invariant (c&(c-1)) == 0,
      candidate_invariant c == 0 || b*c == a,
                   candidate_invariant b < 1,
                   candidate_invariant b < 2*a,
		   candidate_invariant (b*b*b*b&(b-1)) == 0,
		   candidate_invariant (c&(c*c*c-1)) == 0
				{
      assert b*c == a;
      b = b << 1;
      c = c >> 1;
    }
    a = a << 1;
  }
  assert a == (1 << 24);
  return 52;
}

