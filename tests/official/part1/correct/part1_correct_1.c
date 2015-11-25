// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int a;
int b;
int c;
int d;

int havocy()
    ensures a == 5,
    ensures b == 6,
    ensures c == 7,
    ensures d == 8
{
    havoc a;
    assume a == 1;
    havoc b;
    assume b == a + 1;
    havoc c;
    assume c == b + 1;
    havoc d;
    assume d == c + 1;
    havoc a;
    assume a == d + 1;
    havoc b;
    assume b == a + 1;
    havoc c;
    assume c == b + 1;
    havoc d;
    assume d == c + 1;
    return 0;
}
