// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main() {

    int x;
    int y;

	if (x != 5) {
        if (x < 0) {
            z = 0;
        } else {
            assert (z != -1);
            z = x;
        }
        assert z >= 0;
        assert z != 5;
    }

    return 0;
}
