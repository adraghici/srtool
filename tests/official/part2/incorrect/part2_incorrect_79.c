// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;
int z;

int theproc() {
  assume x >= -2147483647;

  int c; 
  c = 0;
  assume x >= 18 && x < 19;
  while(x != 0)
    candidate_invariant c <= (\old(x) + \old(y) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c == y & \old(y),
    candidate_invariant c <= (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c != y - \old(y),
    candidate_invariant c <= (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c - (x < 0 ? - -x : !! x) == (x < 0 ? - -\old(x) + x + x * y : \old(x)),
      candidate_invariant c == y - \old(y),
    candidate_invariant c <= (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c == y - \old(y),
      candidate_invariant 0 ? c <= (\old(x) < 0 ? -\old(x) : \old(x)) : 1,
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c == y - \old(y),
    candidate_invariant c <= (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c == y - \old(y),
      candidate_invariant c <= (\old(x) < 0 ? -\old(x) % \old(y) : \old(x)),
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c == y - \old(y),
    candidate_invariant c <= (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c + (x < 0 ? -x : x) == (\old(x) < 0 ? -\old(x) : \old(x)),
      candidate_invariant c == y - \old(y),
      candidate_invariant c <= (\old(x) < 0 ? \old(x) : \old(x)),
      invariant x == 0 ? (c + (x - 1 + 2 < 0 ^ 1 ^ 2 ^ 3 ? -x : x) == (~~\old(x)  < 0 ? -\old(x) : \old(x))) : 1,
      invariant x == 0 ? c == c + 1 : 1,
      invariant c == y - \old(y) {
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
