// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
	int c;
	c=0;
	int i;
	i=0;

	int x;

	while(i < 4)
	candidate_invariant (c == (i * 3)),
	//candidate_invariant (i >= 0 && i <= 4)
	candidate_invariant (x * x >= c*c)
	{
		x = x + 1;
		int j;
		j=0;
		while(j < 3)
		//candidate_invariant (j >= 0 && j <= 3)
		candidate_invariant (c == i * 3 + j)
		{
			j = j + 1;
			c = c + 1;
			x = x + 1;
		}
		i = i + 1;
	}
	assert(c == 12);
  return 0;
}

