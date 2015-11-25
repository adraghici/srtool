// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
	assert(2 >= 2);
  return 0;
}

