// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
  return 0;
}
