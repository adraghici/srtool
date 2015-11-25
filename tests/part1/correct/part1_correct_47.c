// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
	assert((4 >> 1) == 2);
  return 0;
}
