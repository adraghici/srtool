// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;
int z;

int theproc() requires x + y == z, ensures \result == 52
{
  {
    int i;
    i = 0;
    while(i < 5) invariant i >= 0, invariant i <= 5 {
	i = i + 1;
	{
	  int i;
	  i = 0;
	  while(i < 5) invariant i >= 0, invariant i <= 5 {
	      i = i + 1;
	      {
		int i;
		i = 0;
		while(i < 5) invariant i >= 0, invariant i <= 5 {
		    i = i + 1;
		    {
		      int i;
		      i = 0;
		      assert 0;
		      while(i < 5) invariant i >= 0, invariant i <= 5 {
			  i = i + 1;
			  {
			    int i;
			    i = 0;
			    while(i < 5) invariant i >= 0, invariant i <= 5 {
				i = i + 1;
				{
				  int i;
				  i = 0;
				  while(i < 5) invariant i >= 0, invariant i <= 5 {
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
      }


  }

  {
    int i;
    i = 0;
    while(i < 5) invariant i >= 0, invariant i <= 5 {
	i = i + 1;
	{
	  int i;
	  i = 0;
	  while(i < 5) invariant i >= 0, invariant i <= 5 {
	      i = i + 1;
	      {
		int i;
		i = 0;
		while(i < 5) invariant i >= 0, invariant i <= 5 {
		    i = i + 1;
		    {
		      int i;
		      i = 0;
		      while(i < 5) invariant i >= 0, invariant i <= 5 {
			  i = i + 1;
			  {
			    int i;
			    i = 0;
			    while(i < 5) invariant i >= 0, invariant i <= 5 {
				i = i + 1;
				{
				  int i;
				  i = 0;
				  while(i < 5) invariant i >= 0, invariant i <= 5 {
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
      }


  }
  return 52*2/2;

}
