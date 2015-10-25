int main() {

	int x;
	x = ((1 + 1) <= (0 + 2));
	assert x == 1;

	x = 5 != 7;
	assert x == 1;

	x = x + (x == x) == !(x != x) + x - 1 + 1;
	assert x == 1;

	x = 1 << 2;
	assert x == 4;

	x = 1 << 3;
	assert x == 7 + 1;

	x = 1 << 31;
	assert x == 2147483648;

	x = x + 1;
	assert x == -2147483647;

	x = 15 >> 2;
	assert x == 3;

	x = x >> 10;
	assert x == 0;

	return 0;

}
