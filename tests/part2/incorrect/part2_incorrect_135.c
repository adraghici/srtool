// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
	int start;
	assume(start > 0);
	int i;
	i=start;
	while(i)
	//bound(3) // bound is large enough. assertion should fail.
	{
		i = i - 1;
	}
	
	
	
	if(start > 2)
	{
		assert(0);
	}
  return 0;
}

