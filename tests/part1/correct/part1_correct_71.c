// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{
    int i;
    int j;
    int z;
	
	int res; res=0;

	i=1;
	j=1;

	if(i)
	{
		if(j)
		{
			res=1;
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
			
		}
	}

	assert(res);

  return 0;
}
