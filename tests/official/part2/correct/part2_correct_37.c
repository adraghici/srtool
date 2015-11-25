// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
	int i;
	i=0;
	while(i < 2)
	{
		i = i + 10;
	}
	
	assert(i == 10);
	
  return 0;
}

