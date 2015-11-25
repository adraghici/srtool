// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;
int z;

int theproc() requires x + y == z, ensures \result == 52
{
  int i;
  i = 0;
  while(i < 100) invariant i <= 100 {
    int j;
    j = i;

    if(i > 30) {
      while(j < 200) invariant j <= 200 {
	  int k;
	  k = j;
	  assert 0;
	  if(0) {
	  } else {
	    while(k < 300) invariant k <= 300 {
		k = k + 1;
		assume k != j;
	      }
	  }
	  assert k == 300;
	  j = j + 1;
	}
    } else {
      while(j < 200) invariant j <= 200 {
	  int k;
	  k = j;
          assert i <= 30;
	  while(k < 300) invariant k <= 300 {
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

