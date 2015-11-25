// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int _wfoin24(int i, int j) {
    assume i == 3 || i == 6 || i == 9;
    assume j == 27 || j == 54 || j == 81;
    assert (i % j) == 0;
    return j;
}
