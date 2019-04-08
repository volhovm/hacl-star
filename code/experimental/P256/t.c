#include <inttypes.h>


#include "p256-c/Hacl_Impl_P256.h"

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

uint64_t generateRandom()
{
   return (uint64_t) (((uint64_t) rand() << 33) | rand())%18446744073709551615U;
}


void print_u(uint64_t a)
{
   printf("%" PRIu64 " ", a);
   printf("%u ", (uint32_t) a);
   printf("%u\n", (uint32_t) (a >> 32));
}

void print_uu(uint64_t* a)
{
   print_u(a[0]);
   print_u(a[1]);
   print_u(a[2]);
   print_u(a[3]);
   printf("\n");
}


void print_uu_l (uint64_t* a, int len, bool div)
{
   if (div)
   {
      int counter = 0;
      int i = 0;
      for (i = len; i < len; i++)
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


void testToDomain(uint64_t * basePoint)
{
   uint64_t * basePointInDomain = (uint64_t*) malloc (sizeof (uint64_t) * 12);
   pointToDomain(basePoint, basePointInDomain);
   uint64_t * expectedResult = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   expectedResult[0] = 8784043285714375740uL;
   expectedResult[1] = 8483257759279461889uL;
   expectedResult[2] = 8789745728267363600uL;
   expectedResult[3] = 1770019616739251654uL;

   expectedResult[4] = 15992936863339206154uL;
   expectedResult[5] = 10037038012062884956uL;
   expectedResult[6] = 15197544864945402661uL;
   expectedResult[7] = 9615747158586711429uL;
 
   expectedResult[8] = 1uL;
   expectedResult[9] = 18446744069414584320uL;
   expectedResult[10] = 18446744073709551615uL;
   expectedResult[11] = 4294967294uL;
 
   bool flag = true;
   for (int i = 0; i< 12; i++)
   {
      flag = flag && (expectedResult[i] & basePointInDomain[i]);
   }

   if (flag)
      printf("%s\n", "The test is correct"); 
   else
      printf("%s\n", "The test has not passed");
}


int main()
{
   time_t t; 
   srand((unsigned) time(&t));

   uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   uint64_t* q = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 117);
   
   basePoint[0] = 17627433388654248598uL;
   basePoint[1] = 8575836109218198432uL;
   basePoint[2] = 17923454489921339634uL;
   basePoint[3] = 7716867327612699207uL;

   basePoint[4] = 14678990851816772085uL;
   basePoint[5] = 3156516839386865358uL;
   basePoint[6] = 10297457778147434006uL; 
   basePoint[7] = 5756518291402817435uL;

   basePoint[8] = 1uL;
   basePoint[9] = 0uL;
   basePoint[10] = 0uL;
   basePoint[11] = 0uL;


   q[0] = 11964737083406719352uL;
   q[1] = 13873736548487404341uL;
   q[2] = 9967090510939364035uL;
   q[3] = 9003393950442278782uL;

   q[4] = 11386427643415524305uL;
   q[5] = 13438088067519447593uL;
   q[6] = 2971701507003789531uL; 
   q[7] = 537992211385471040uL;

   q[8] = 1uL;
   q[9] = 0uL;
   q[10] = 0uL;
   q[11] = 0uL;

   pointToDomain(basePoint, basePoint);
   pointToDomain(q, q);
   point_add(basePoint, q, resultPoint, tempBuffer);

   // ?point_double(basePoint, resultPoint, tempBuffer);
   norm(resultPoint, resultPoint, tempBuffer);
   print_uu_l(resultPoint, 12, false);

   /*Hacl_Impl_P256_pointToDomain(q, q);
   
   Hacl_Impl_P256_point_double(basePoint, resultPoint, tempBuffer);
   Hacl_Impl_P256_norm(resultPoint, resultPoint, tempBuffer);
   print_uu_l(resultPoint, 12, false);

   Hacl_Impl_P256_point_add(basePoint, q, resultPoint, tempBuffer);
   Hacl_Impl_P256_norm(resultPoint, resultPoint, tempBuffer);
*/
   // print_uu_l(basePoint, 12, false); 

}


/*cc -I /home/nkulatov/HaclOct2018/hacl-star//code/lib/kremlin -I /home/nkulatov/HaclOct2018/hacl-star//specs -I /home/nkulatov/new/kremlin/kremlin/kremlib -I /home/nkulatov/HaclOct2018/hacl-star//code/hash -I /home/nkulatov/new/kremlin/kremlin/include -I /home/nkulatov/new/kremlin/kremlin -I /home/nkulatov/new/kremlin/kremlin/kremlib/extracted -L /home/nkulatov/new/kremlin/kremlin/kremlib/out -I /home/nkulatov/HaclNO/hacl-star/code/P256/p256-c/  -o test-p256.exe Hacl_Spec_Curve25519_Field64_Core.c Hacl_Spec_P256_Core.c Hacl_Spec_P256_SolinasReduction.c Hacl_Spec_P256_MontgomeryMultiplication.c  Hacl_Impl_P256.c t.c -lkremlib && ./test-p256.exe  */
/* make p256-c/Hacl_P256.c  */