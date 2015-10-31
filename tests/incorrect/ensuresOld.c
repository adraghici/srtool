// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;

int func()
  ensures \old(x) > 1
{
    x = 2;
	return x;
}