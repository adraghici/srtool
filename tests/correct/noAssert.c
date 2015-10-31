// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func() {
    int x;
    x = 1;
    return x;
}