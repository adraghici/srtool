// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main(int i, int j, int z)
{
	int a;
	int b;
	int c;
	int d;
	a=0;
	b=0;
	c=0;
	d=0;

	if(i)
	{
		if(j)
		{
			
		}
		else
		{
			assert(0);
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

  return 0;
}
