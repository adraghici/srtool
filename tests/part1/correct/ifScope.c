// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {
    int x;
    x = 5;

    if(x >= 5){
        int x;
        x = 6;
    }

    assert x == 5;

    return 0;
}