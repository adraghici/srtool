// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
	int i;
	int j;
	int z;
	i=0;

	int n;
	assume(n >= 50000);
	assume(n <= 100000);

	while(i < n)
	candidate_invariant (i<=n),
	candidate_invariant (i>=0)
	{
		i = i + 1;
		j=0;
		z=0;
		while(j < 3)
		candidate_invariant (j<=3),
		candidate_invariant (j>=0),
		invariant (z == i * j)
		{
			z = z + i;
			j = j + 1;
		}
		assert(z==i*3 + 1);
	}
	
  return 0;
}

