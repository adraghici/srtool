// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main() {

	int x;
	int y;
	int z;

	x = y;

	if (x > z) {
		x = x + 1;
		assert x > y;
		y = y + 1;
	} else {
		x = x + y;
		assert x != y;
	}

	return 0;
}
