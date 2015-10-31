// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func() {
	int x;
	int y;
	int z;
	if(x < y) {
    	if(y < z) {
    		assert(x < z);
    	}
    }
	return 1;
}