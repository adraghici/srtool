// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func() {
	int temp;
	int a;
	int b;
	int c;
	int d;
	d = 9;
	if(a != b && a != c && b != c) {
		temp = a;
		a = b;
		b = c;
		c = temp;
		assert(a != b && a != c && b != c);
	}
	return 1;
}