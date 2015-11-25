// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"


int main()
{
	int i;
	int j;
	i=0;
	j=1;

	while(i < 5)
	{
		i = i + j;
	}

	// OK, as j is not modified
	assert(j == 1);
	
  return 0;
}
