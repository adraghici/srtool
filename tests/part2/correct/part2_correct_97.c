// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int x;
int y;
int z;

int theproc() requires x + y != z, candidate_ensures \result == 52 {
  while(x > 0) invariant x + y != z,
		 candidate_invariant x + y != z,
		 candidate_invariant x + y != z,
		 candidate_invariant x % y % z,
		 candidate_invariant x + y % z,
		 invariant 1,
		 candidate_invariant x + y / z,
                 candidate_invariant x / x != 1,
		 candidate_invariant x + y * z,
		 candidate_invariant x + y & z,
		 invariant !!!!!0,
		 candidate_invariant y + y || z,
		 candidate_invariant z + y && z,
		 candidate_invariant x + z <= z,
		 candidate_invariant x + z >= z,
		 candidate_invariant x + y > y
{
    x = x - 1;
    y = y + 1;
  }
  assert x + y != z;
  return 52;
}
