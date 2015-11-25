// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main(int _i, int _j, int _p)
{
    int i;
    int j;
    int p;
    i = _i;
    j = _j;
    p = _p;
	i=0;
	j=0;
	
	p = (i == j);
	assert(p);
  return 0;
}
