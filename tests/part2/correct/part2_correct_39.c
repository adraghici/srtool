// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
	int i;
	int n;
	assume(n >= 50000);
	assume(n <= 100000);
	assume((n%4)==0);

	i=0;
	while(i < n)
	{
		i = i + 2;
	}
	
	assert(i == n);
	
  return 0;
}

