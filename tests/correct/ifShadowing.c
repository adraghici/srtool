// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {
    int x;
    x = 5;

    if(x >= 5){
        x = 7;
        int x;
        x = 6;
    }

    assert x == 7;

    return 0;
}