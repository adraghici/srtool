// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int inc(int n, int max)
    requires n <= max,
    ensures \result == max
{
    int r;
    if(n == max) {
        r = max;
    } else {
        r = inc(n + 1, max);
    }
    return r;
}
