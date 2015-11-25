// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int func()
  ensures \result >= 1
{
    x = 2;
	return x;
}