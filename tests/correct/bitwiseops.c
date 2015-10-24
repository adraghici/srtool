int main() {
	int a;
	a = 4 & 7;
	assert a == 4;

	a = 1 | 2 ^ 3 & 4 | 5;
	assert a == 7;

	return 0;
}
