// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main(int i, int j)
{
    int z;
	if(i==j)
	{
	}
	else
	{
		z = 5;
	}
	
	if(i != j)
	{
		assert(z == 5);
	}
  return 0;
}
