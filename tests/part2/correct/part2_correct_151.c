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
		if(1)
		{
			j=2;
		}
		else
		{
			j=1;
		}

		assert(j==2);
	}

	
  return 0;
}
