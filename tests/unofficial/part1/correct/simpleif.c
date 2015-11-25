// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {

    int x;
    int y;

    x = 4;
    y = 3;

    if (x == 4) {
        x = x + 2;
        assert x == 6;
        if (y == 2) {
            assert y == 2;
        } else {
            y = y * 2 + y;
            assert 9 == y;
        }
    }

    return 0;
}
