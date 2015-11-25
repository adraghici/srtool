// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;
int z;

int theproc() candidate_requires x + y == z, candidate_ensures \result == 52
{
  int i;
  i = 0;
  while(i < 100) candidate_invariant 0, invariant i <= 100, candidate_invariant i != 1,  candidate_invariant i != 2,  candidate_invariant i != 3,  candidate_invariant i != 4,  candidate_invariant i != 5 {
    int j;
    j = i;

    if(i > 30) {
      while(j < 200) candidate_invariant 0, invariant j <= 200, candidate_invariant i != 1,  candidate_invariant i != 2,  candidate_invariant i != 3,  candidate_invariant i != 4,  candidate_invariant i != 5, candidate_invariant j != 1,  candidate_invariant j != 2,  candidate_invariant j != 3,  candidate_invariant j != 4,  candidate_invariant j != 5 {
	  int k;
	  k = j;
	  if(0) {
	  } else {
	    while(k < 300) candidate_invariant 0, invariant k <= 300, candidate_invariant i != 1,  candidate_invariant i != 2,  candidate_invariant i != 3,  candidate_invariant i != 4,  candidate_invariant i != 5, candidate_invariant k != 1,  candidate_invariant k != 2,  candidate_invariant k != 3,  candidate_invariant k != 4,  invariant k != 5 {
		k = k + 1;
		assume k != j;
	      }
	  }
	  assert k == 300;
	  j = j + 1;
	}
    } else {
      while(j < 200) candidate_invariant 0, invariant j <= 200, candidate_invariant i != 1,  candidate_invariant i != 2,  candidate_invariant i != 3,  candidate_invariant i != 4,  candidate_invariant i != 5 {
	  int k;
	  k = j;
          assert i <= 30;
	  while(k < 300) candidate_invariant 0, invariant k <= 300, candidate_invariant i != 1,  candidate_invariant i != 2,  candidate_invariant i != 3,  candidate_invariant i != 4,  candidate_invariant i != 5, candidate_invariant i == 1,  candidate_invariant i == 2,  candidate_invariant i == 3,  candidate_invariant i == 4,  candidate_invariant i == 5 {
              if(k == k - 1) {
		k = k - 1;
	      }
	      k = k + 1;
	      assume k != j;
	    }
	  assert k == 300;
	  j = j + 1;
	}
    }
    assert j == 200;
    i = i + 1;
  }
  assert i == 100;
  return 51 - 1 + 2;
}

