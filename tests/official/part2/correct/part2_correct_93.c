// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc() {

  int x;
  x = 0;
  while(x < 99)
    candidate_invariant x != 0,
    candidate_invariant x != 1,
    candidate_invariant x != 2,
    candidate_invariant x != 3,
    candidate_invariant x != 4,
    candidate_invariant x != 5,
    candidate_invariant x != 6,
    candidate_invariant x != 7,
    candidate_invariant x != 8,
    candidate_invariant x != 9,
    candidate_invariant x != 10,
    candidate_invariant x != 11,
    candidate_invariant x != 12,
    candidate_invariant x != 13,
    candidate_invariant x != 14,
    candidate_invariant x != 15,
    candidate_invariant x != 16,
    candidate_invariant x != 17,
    candidate_invariant x != 18,
    candidate_invariant x != 19,
    candidate_invariant x != 20,
    candidate_invariant x != 21,
    candidate_invariant x != 22,
    candidate_invariant x != 23,
    candidate_invariant x != 24,
    candidate_invariant x != 25,
    candidate_invariant x != 26,
    candidate_invariant x != 27,
    candidate_invariant x != 28,
    candidate_invariant x != 29,
    candidate_invariant x != 30,
    candidate_invariant x != 31,
    candidate_invariant x != 32,
    candidate_invariant x != 33,
    candidate_invariant x != 34,
    candidate_invariant x != 35,
    candidate_invariant x != 36,
    candidate_invariant x != 37,
    candidate_invariant x != 38,
    candidate_invariant x != 39,
    candidate_invariant x != 40,
    candidate_invariant x != 41,
    candidate_invariant x != 42,
    candidate_invariant x != 43,
    candidate_invariant x != 44,
    candidate_invariant x != 45,
    candidate_invariant x != 46,
    candidate_invariant x != 47,
    candidate_invariant x != 48,
         invariant x <= 100, invariant (x % 2) == 0 {
      int t;
      t = x;
      havoc x;
      assume x == t + 2;
    }
  assert x == 100;
  return 0;
}
