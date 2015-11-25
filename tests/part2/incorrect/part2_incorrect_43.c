// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
	int i;
	i=0;
	
	int n;
	assume(n >= 50000);
	assume(n <= 100000);
	
	while(i < n)
	{
		i = i + 2;
	}
	
	assert(i == n+1);
	
  return 0;
}

