// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {
  assert (16 / 2 * 2 / 2 * 2) == 16;
  return 0;
}
