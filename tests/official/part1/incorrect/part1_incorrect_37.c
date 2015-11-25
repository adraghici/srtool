// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int iffy(int a, int b, int c, int d)
    ensures \result == 0,
    requires a > b,
    requires b > c,
    requires c > d
{
    int x;
    if (d < c) {
        if (c < b) {
            if(b < a) {
                if(a > b) {
                    if(b > c) {
                        if(c > d) {
                            x = 4242;
                        } else {
                            x = 1;
                        }
                    } else {
                        x = 2;
                    }
                } else {
                    x = 3;
                }
            } else {
                x = 4;
            }
        } else {
            x = 5;
        }
    } else {
        x = 6;
    }

    return x;
}
