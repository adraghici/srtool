// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int main()
    requires 2 == 2,
    ensures \result == (\old(x) & (100 || 23121))
{
    int y;
    y = x;

    return y & 1;
}