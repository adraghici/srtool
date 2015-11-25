// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
    int a;
	a = 2;
	
	havoc a;
	a = 3;

	assert(a == 3);
  return 0;
}
