// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// \old(x) should refer to the global variabile int x!

int x;

int main()
{
	int x;
	assume x == \old(x);
	assert (2 > 3);

	return 0;
}
