// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{
    int i;
    int j;
    int z;
	
	int res; res=0;

	i=1;
	j=0;

	if(i)
	{
		if(j)
		{
			
		}
		else
		{
			res=1;
		}
	}
	else
	{
		if(z)
		{
			
		}
		else
		{
			
		}
	}

	assert(res);

  return 0;
}
