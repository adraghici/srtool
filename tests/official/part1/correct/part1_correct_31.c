// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {
  assert (0 ? 42 : 0 ? 54 : 0 ? 65 : 7) == 7;
  return 0;
}

