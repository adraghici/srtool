// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int _wfoin24(int i, int j) {
    assume i == 3 && j == 27 || i == 6 && j == 54 || i == 9 && j == 81;
    assert (j % i) == 0;
    return j;
}
