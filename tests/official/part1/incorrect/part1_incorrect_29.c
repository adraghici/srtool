// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main() {
  assert (0 ? 42 : 0 ? 54 : 0 ? 65 : 7) == 0;
  return 0;
}

