// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int foo()
    candidate_requires y == 2 * x,
    candidate_requires x % 2 == 0,
    candidate_ensures x >= 0,
    candidate_ensures y == 2 * x,
    candidate_ensures y % 2 == 0
{
    if (x < 1000) {
        x = x + 1;
        y = y + 2;
        int h;
        h = bar();
    }

    return 0;
}

int bar()
    candidate_requires y == 2 * x,
    candidate_requires x % 2 == 0,
    ensures y == 2 * x,
    candidate_ensures y % 2 == 0
{
    if (x > 0) {
        x = x - 1;
        y = y - 2;
        int h;
        h = foo();
    }

    return 0;
}
