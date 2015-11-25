// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int theproc(int a) requires a == 1 || a == 2 || a == 4 || a == 8 || a == 16 || a == 32 || a == 64 || a == 128 || a == 256 || a == 512, ensures \result == a {

  int d;
  d = a;
  while(d > 0) candidate_invariant d == 0 || d == 1 || d == 2 || d == 4 || d == 8 || d == 16 || d == 32 || d == 64 || d == 128 || d == 256 || d == 512,
		 candidate_invariant d == 0 || d == 1 || d == 2 || d == 4 || d == 8 || d == 16 || d == 32 || d == 64 || d == 128 || d == 256 || d == 512,
		 candidate_invariant d == 0 || d == 1 || d == 2 || d == 4 || d == 8 || d == 16 || d == 32 || d == 64 || d == 128 || d == 256 || d == 512,
		 candidate_invariant d == 0 || d == 8 || d == 16 || d == 32 || d == 64 || d == 128 || d == 256 || d == 512,
		 candidate_invariant d == 0 || d == 1 || d == 2 || d == 4 || d == 8 || d == 16,
		 candidate_invariant d != 0,
		 candidate_invariant d != 1,
		 candidate_invariant d != 2,
		 candidate_invariant d != 3,
		 candidate_invariant d != 4,
		 candidate_invariant d != 5,
		 candidate_invariant d != 6,
		 candidate_invariant d != 7,
		 candidate_invariant d != 8
 {
      d = d / 2;
      if(d > 1) {
	assert (d/3)*2 == d;
      }
    }
  assert d == 0;
  return d + a;
}
