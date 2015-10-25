// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int a;

int foo() {

    int x;
    havoc x;

	havoc a;

	return 0;
}
