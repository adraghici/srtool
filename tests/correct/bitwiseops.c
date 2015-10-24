int main() {
	int a;
	a = 4 & 7;
	assert a == 4;

	a = 1 | 2 ^ 3 & 4 | 5;
	assert a == 7;

	int b;
	b = 5;
	b = +-!~b;
	assert b == 0;

	int c;
	c = -+-+!!(~b - 1 * 1);
	assert c == 1;

	c = ~-1;
	assert c == 0;

	c = ~0;
	assert c == -1;

	c = ~1;
	assert c == -2;

	c = 0;
	c = !(!c);
	assert c == 0;

	return 0;
}
