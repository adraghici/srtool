// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    if (1 == 1) {

    } else {
        int w;
        w = 1;
        assert (w == 1);
    }

    return 0;
}
