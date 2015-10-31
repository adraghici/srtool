// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int a;
int b;

int func() {
	assume a > -2147483647;
	assume b > -2147483647;
	assume a < 2147483648;
	assume b < 2147483648;

	if(a < 0) {
		assume(b < 0);
		assert(a + b < 0);
	} else {
		assume(b >= 0);
		assert(a + b >= 0);
	}
	return 1;
}