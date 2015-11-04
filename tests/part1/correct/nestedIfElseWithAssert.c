// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func() {
	int x;
	int y;
	int z;

	assume x >= y >= z > -2147483647;
	assume x <= y <= z < 2147483648;

	if(x < y) {
    	if(y < z) {
    		assert(x < z);
    	}else{
    		assert(x >= z);
    	}
    }
	return 1;
}