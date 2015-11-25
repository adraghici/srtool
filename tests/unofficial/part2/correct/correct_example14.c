// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

// Isn't this cute?

int x;

int f() ensures \result >= \old(x) + 5 {
    return x + 5;
}

int g() {
    int h;
    h = h();
    assert x == 5;

    int y;
    y = f();
    assert y >= 10;
    return 0;
}

int h()
    ensures x == 5
{
    x = 5;
    return 0;
}
