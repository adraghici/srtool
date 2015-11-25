// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"


int main()
{
	int i;
	i=0;
	int j;
	j=0;
	while(i < 5)
	{
		i = i + 1;
		j=0;
	}
	
	// fails because j is in modset
	assert(j == 0);
  return 0;
}
