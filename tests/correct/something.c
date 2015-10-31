// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {

   int x;
   int y;

   int a;

   if (x >= 0) {
      a = 0;
      a = a + 2;
      if (y >= 0) {
         a = a + 4;
         assert (x >=0 && y >= 0 && x * y >= 0);
      }
      assert (a % 2 == 0);
   } else {
      a = 1;
      a = a + 2;
      if (y < 0) {
         a = a + 4;
         assert (x < 0 && y < 0);
      }

      assert ((a + 1) % 2 == 0);
   }

   return 0;

}