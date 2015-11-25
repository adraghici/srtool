// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"


int main()
{
	int i;
	int j;
	i=0;
	j=1;

	while(i < 5)
	invariant (j==1)
	{
		i = i + j;
		if(1)
		{
			j=j+1;
		}
		else
		{
		}
	}

  return 0;
}
