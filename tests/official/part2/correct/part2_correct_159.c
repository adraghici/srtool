// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int a, int b, int c)
    requires a != b,
    requires a != c,
    requires b != c
{
    int x;
    int y;
    int z;

    x = a;
    y = b;
    z = c;

    int i;

    i = 0;
    while(i < 100) invariant x != y, invariant x != z, invariant y != z {
        int temp;
        temp = x;
        x = y;
        y = z;
        z = temp;
        i = i + 1;
    }
    assert x != y;
    assert x != z;
    assert y != z;
    
    return 0;

}
