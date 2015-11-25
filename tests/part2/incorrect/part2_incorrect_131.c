// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
	int i;
	i=0;
	while(i < 0)
	//bound(0)
	invariant (i == 100)
	{
	}
	
  return 0;
}

