// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()
{
    int i;	int j; int z;
{
	if(i==j)
	{
	 z = 5;
	}
}
	
	assert(z == 5);
  return 0;
}
