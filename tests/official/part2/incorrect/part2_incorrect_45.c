// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int main()
{
 int i;
 int iterations;
 i=0;
 
 // make iterations positive, but otherwise unconstrained
 assume(iterations > 50000);

 	int a;
	int b;
	int c;
	int d;
	int e;
	int f;
	int g;
	int h;

	a=1;
	b=1;
	c=1;
	d=1;
	e=1;
	f=1;
	g=1;
	//h=1;

 
 while(i < iterations)
 {
	i = i + 1;
	a = a - 66;
	b = b - 166;
	c = c - 1;
	d = d + 1;
	e = e + 127;
	f = f + i - 66;
	g = g;
	h = h - 66;
 }
 

i = i + a + b + c;
i = i - a - b - c;


 assert(i == iterations + 1);
 
  return 0;
}

