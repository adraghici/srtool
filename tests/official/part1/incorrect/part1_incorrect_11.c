// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int lotsaplus() {
    int i;
    i = -5;
    int t;
    t = + + + - + + + + + + + + +i;
    assert t == -5;
    return +t;
}
