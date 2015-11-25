// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{
    int i;
    int j;
    int z;
	
	int res; res=0;

	i=0;
	z=1;

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
			res=1;
		}
		else
		{
			
		}
	}

	assert(res);

  return 0;
}
