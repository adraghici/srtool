// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main() {
  assert 1 == (16 / 2 * 2 / 2 * 2);
  return 0;
}

