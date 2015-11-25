// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
    int i; int j; int z;
	
	int res; res=0;

	i=0;
	z=0;

	if(i)
	{
		if(j)
		{
			
		}
		else
		{
			
		}
	}
	else
	{
		if(z)
		{
			
		}
		else
		{
			res=1;
		}
	}

	assert(!res);

  return 0;
}
