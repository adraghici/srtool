// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {

    int x;

    x = 1 << 31;
    assert x == 2147483648;

    x = x + 1;
    assert x == -2147483647;

    int y;

    y = x << 32;
    assert y == 0;

    y = x >> 32;
    assert y == 0;

	return 0;
}