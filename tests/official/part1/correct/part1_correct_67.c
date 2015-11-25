// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
	assert((3 && 2) == 1);
  return 0;
}
