// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {

   int x;
   int y;
   int z;

   int a;

   if (x >= 0) {

      a = 0;
      a = a + 2;
      assert (a == 2);
      assert (!(x < 0));

      if (y >= 0) {
         a = a + 4;
         assert (a == 6);
         assert (!(x < 0) && !(y < 0));

         if (z >= 0) {
            a = a + 6;
            assert (a == 12);
            assert (!(x < 0) && !(y < 0) && !(z < 0));
         } else {
            a = a + 8;
            assert (a == 14);
            assert (!(x < 0) && !(y < 0) && !(z >= 0));
         }

      } else {

         a = a + 10;
         assert (a == 12);
         assert (!(x < 0) && !(y >= 0));

         if (z >= 0) {
            a = a + 12;
            assert (a == 24);
            assert (!(x < 0) && !(y >= 0) && !(z < 0));
         } else {
            a = a + 14;
            assert (a == 26);
            assert (!(x < 0) && !(y >= 0) && !(z >= 0));
         }

      }

      assert (a % 2 == 0 && x >= 0 && (y >= 0 || y < 0) && (z >= 0 || z < 0));

   } else {

      a = 1;
      a = a + 2;
      assert (a == 3);
      assert (!(x >= 0));

      if (y >= 0) {
         a = a + 4;
         assert (a == 7);
         assert (!(x >= 0) && !(y < 0));

         if (z >= 0) {
            a = a + 6;
            assert (a == 13);
            assert (!(x >= 0) && !(y < 0) && !(z < 0));
         } else {
            a = a + 8;
            assert (a == 15);
            assert (!(x >= 0) && !(y < 0) && !(z >= 0));
         }

      } else {

         a = a + 10;
         assert (a == 13);
         assert (!(x >= 0) && !(y >= 0));

         if (z >= 0) {
            a = a + 12;
            assert (a == 25);
            assert (!(x >= 0) && !(y >= 0) && !(z < 0));
         } else {
            a = a + 14;
            assert (a == 27);
            assert (!(x >= 0) && !(y >= 0) && !(z >= 0));
         }

      }

      assert (a % 2 == 1 && x < 0 && (y >= 0 || y < 0) && (z >= 0 || z < 0));

   }

   return 0;

}