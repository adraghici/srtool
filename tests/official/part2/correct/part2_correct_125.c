// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
	int i;
	i=0;
	while(i < 0)
	//bound(0)
	{
	}
  return 0;
}

