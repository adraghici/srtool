// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int theproc() {

  int a;
  a = 0;

  {
    int i;
    i = 0;
    while(i < 1) {
      assert a == 0;
      a = a + 1;
      i = i + 1;
      {
        int i;
	i = 0;
	while(i < 1) {
	  assert a == 1;
	  a = a + 1;
	  i = i + 1;
	  {
	    int i;
	    i = 0;
	    while(i < 1) {
	      assert a == 2;
	      a = a + 1;
	      i = i + 1;
	      {
		int i;
		i = 0;
		assert 0;
		while(i < 1) {
		  assert a == 3;
		  a = a + 1;
		  i = i + 1;
		  {
		    int i;
		    i = 0;
		    while(i < 1) {
		      assert a == 4;
		      a = a + 1;
		      i = i + 1;
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
		      
