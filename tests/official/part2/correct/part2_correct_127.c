// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{
	int i;
	i=0;
	while(i < 2)
	invariant (i >= 0),
	invariant (i <= 2)
	{
		i = i + 1;
	}
	
	assert(i == 2);
	
  return 0;
}

