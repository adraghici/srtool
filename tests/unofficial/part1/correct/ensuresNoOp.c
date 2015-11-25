// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int fun()
  ensures x == \old(x)
{
	return 1;
}
