// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int func()
 ensures \result == 7
{
    int x;
    x = 5;
    if (x == 5) {
        x = 6;
        int x;
        x = 7;
    }
    return x;
}
