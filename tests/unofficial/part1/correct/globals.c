// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int foo() {
    x = x + 1;
    y = y + 2;

	return 0;
}

int bar() {
    x = x + 1;
    y = y + 2;

    return 0;
}
