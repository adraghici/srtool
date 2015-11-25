// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()

{
	assert((2 ^ 3) == 3);
  return 0;
}
