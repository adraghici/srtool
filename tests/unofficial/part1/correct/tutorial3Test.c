// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int a;
int b;
int c;

int test() {
    a = 2; b = 3; c = 4;

    assert(a != b && a != c && b != c);
    havoc a;
    havoc b;
    havoc c;
    assume(a != b && a != c && b != c);

    a = a + 1;
    b = b + 1;
    c = c + 1;

    assert(a != b && a != c && b != c);
    havoc a;
    havoc b;
    havoc c;
    assume(a != b && a != c && b != c);

    assert(a != b);
    return 0;
}
