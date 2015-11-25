// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int func()
  ensures x >= 1
{
	x = 1;
	if(x <= 1){
		x = 9;
	}else{
		x = 5;
	}
	return 1;
}