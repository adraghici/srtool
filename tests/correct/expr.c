int main() {

	int x;
	x = ((1 + 1) <= (0 + 2));
	assert x == 1;

	x = 5 != 7;
	assert x == 1;

	x = x + (x == x) == !(x != x) + x - 1 + 1;
	assert x == 1;

	return 0;

}
