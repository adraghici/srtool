// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

// Isn't this cute?

int x;

int f() ensures \result >= \old(x) + 5 {
    return x + 5;
}

int g() {
    x = 5;
    int y;
    y = f();
    assert y >= 10;
    return 0;
}
