// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// \old(x) should refer to the global variable int x!

int x;
int x;
int x;
int x;

int main()
{
	x = 7;
	int x;
	assume x == \old(x);
	assert (2 > 3);

	return 0;
}
