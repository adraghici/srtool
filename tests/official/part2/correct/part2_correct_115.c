// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc() {

  int a;
  a = 0;

  {
    int t;
    int i;
    assume i == 0;
    while(i < 1) {
      assert a == 0;
      havoc t; assume a == t; assume a == t + 1;
      havoc t; assume i == t; assume i == t + 1;
      assert i == 1;
      {
        int i;
	assume i == 0;
	while(i < 1) {
	  assert a == 1;
          havoc t; assume a == t; assume a == t + 1;
          havoc t; assume i == t; assume i == t + 1;
	  assert i == 1;
	  {
	    int i;
	    assume i == 0;
	    while(i < 1) {
	      assert a == 2;
	      havoc t; assume a == t; assume a == t + 1;
	      havoc t; assume i == t; assume i == t + 1;
	      assert i == 1;
	      {
		int i;
		assume i == 0;
		while(i < 1) {
		  assert a == 3;
		  havoc t; assume a == t; assume a == t + 1;
		  havoc t; assume i == t; assume i == t + 1;
		  assert i == 1;
		  {
		    int i;
		    assume i == 0;
		    while(i < 1) {
		      assert a == 4;
		      havoc t; assume a == t; assume a == t + 1;
		      havoc t; assume i == t; assume i == t + 1;
		      assert i == 1;
		    }
		  }
		}
	      }
	    }
	  }
	}
      }
    }
  }
  assert a == 5;
  return 0;
}
		      
