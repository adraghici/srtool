// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
	int i;
	i=0;
	while(i < 2)
	//bound(2)
	invariant (i >= 0),
	invariant (i <= 2)
	{
		i = i + 1;
	}
	
	assert(i == 3);
	
  return 0;
}

