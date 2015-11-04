// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {
	int x;
    x = 1073741824;

    int y;
    y = x << 1;
    assert (y == -2147483648);

    y = x << 32;
    assert (y == 0);

    y = x << 100;
    assert (y == 0);

    y = x >> 32;
    assert (y == 0);

    y = x >> 100;
    assert (y == 0);

    y = x >> 1;
    assert (y == 536870912);

    x = -2147483648;
    y = x >> 31;
    assert (y == -1);

    x = 1;
    y = x << 31;
    assert (y == -2147483648);


	return 0;
}
