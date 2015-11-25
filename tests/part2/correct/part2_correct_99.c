// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int x;
int y;
int z;

int theproc() requires x + y == z, ensures \result == 52
{
  int i;
  i = 0;
  while(i < 100) candidate_invariant i <= 100, candidate_invariant i + 1 > 100, candidate_invariant i > 100, candidate_invariant i > 1000, candidate_invariant i <= 100, candidate_invariant i + 100, candidate_invariant i > 100000 {
    int j;
    j = i;
    while(j < 200) candidate_invariant j <= 200, candidate_invariant j > 200, candidate_invariant j > 20000 + j, candidate_invariant j > j << j >> j, candidate_invariant j != j << 2 >> 2, candidate_invariant j - j + j * i * i {
      int k;
      k = j;
      while(k < 300) candidate_invariant k <= 300 + i + i*2, candidate_invariant k ^ i*i, candidate_invariant k <= 300, candidate_invariant k <= 300, candidate_invariant k <= 300, candidate_invariant i*j*k != 300 {
	k = k + 1;
        assume k != j;
      }
      assert k == 300;
      j = j + 1;
    }
    assert j == 200;
    i = i + 1;
  }
  assert i == 100;
  return 52;
}

