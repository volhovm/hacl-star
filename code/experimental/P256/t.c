#include <inttypes.h>

#include "Hacl_Impl_P256.c"
#include "Hacl_Spec_Curve25519_Field64_Definition.c"


#include "test.c"

#include <stdio.h>
#include <stdlib.h>

/*void print_u(uint64_t a)
{
	printf("%" PRIu64 " ", a);
   printf("%u ", (uint32_t) a);
   printf("%u\n", a >> 32);
}

uint64_t generateRandom()
{
   return (uint64_t) (((uint64_t) rand() << 33) | rand())%18446744073709551615U;
}

void print_uu(uint64_t* a)
{
   print_u(a[3]);
   print_u(a[2]);
   print_u(a[1]);
   print_u(a[0]);
   printf("\n");
}

void print_uu_l (uint64_t* a, uint32_t len, bool div)
{
   if (div)
   {
      int counter = 0;
      int i = 0;
      for (i = 0; i < len; i++)
      {
         printf("%d\n",counter );
         if (counter == 4)
            {
               printf("\n");
               printf("\n");
               counter = 0;
            }
         print_u(a[i]);
         counter = counter +1;      


      }

   }
   else
   {
      int i = 0;
      for (i = 0; i< len; i++)
      {
         printf("%d", i);
         printf("%s", "   " );
         print_u(a[i]);
      }
   }
}

*/
int main()
{
   time_t t; 
   srand((unsigned) time(&t));

   uint64_t *uint64_t arg1 = (uint64_t *) malloc (sizeof (uint64_t) * 4);
   uint64_t *uint64_t arg2 = (uint64_t *) malloc (sizeof (uint64_t) * 4);
   uint64_t *uint64_t result = (uint64_t *) malloc (sizeof (uint64_t) * 4);

   for (int i = 0; i< 4; i++)
   {
      arg1[i] = generateRandom();
   }

   sleep(10);

   for (int i = 0; i< 4; i++)
   {
      arg2[i] = generateRandom();
   }
   
   print_uu(arg1);
   print_uu(arg2);
   Hacl_Impl_P256_p256_add(result, arg1, arg2);
   print_uu(result);


sdf

/*   uint64_t* point = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   uint64_t* result = (uint64_t *) malloc(sizeof (uint64_t) * 12);
   uint64_t* temp = (uint64_t *) malloc (sizeof (uint64_t) * 53);

// x
   point[0] = 1;
   point[1] = 0;
   point[2] = 0;
   point[3] = 0;

// y
   point[0] = 1;
   point[1] = 0;
   point[2] = 0;
   point[3] = 0;

// z
   point[0] = 0;
   point[1] = 0;
   point[2] = 0;
   point[3] = 0;asdas

         
   print_uu_l(point, 4, false);
   print_uu_l(point + 4, 4, false);
   print_uu_l(point + 8, 4, false);*/


}


/* cc -I /home/nkulatov/HaclOct2018/hacl-star//code/lib/kremlin -I /home/nkulatov/HaclOct2018/hacl-star//specs -I /home/nkulatov/new/kremlin/kremlin/kremlib -I /home/nkulatov/HaclOct2018/hacl-star//code/hash -I /home/nkulatov/new/kremlin/kremlin/include -I /home/nkulatov/new/kremlin/kremlin -I /home/nkulatov/new/kremlin/kremlin/kremlib/extracted -L /home/nkulatov/new/kremlin/kremlin/kremlib/out -o test-p256.exe t.c -lkremlib */