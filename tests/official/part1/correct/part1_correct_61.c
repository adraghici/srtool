// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
	assert(2 <= 3);
  return 0;
}
