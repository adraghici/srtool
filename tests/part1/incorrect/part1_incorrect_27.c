// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main() {
  assert (1 ? 2 : 3 ? 4 : 5 ? 6 : 7) == 7;
  return 0;
}

