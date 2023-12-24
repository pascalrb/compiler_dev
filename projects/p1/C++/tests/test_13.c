#include <stdio.h>
#include <math.h>

int compare(float a, float b, float epsilon) {
  return fabs(a - b) < epsilon;
}

float determinant(float *arr, int rows, int cols)
{
  float det = 0;
  float submatrix[rows - 1][cols - 1];
  int i, j, k, l;

  if (rows == 2) {
    return arr[0] * arr[3] - arr[1] * arr[2];
  } else if (rows == 3)
    {
      return arr[0] * arr[4] * arr[8] + arr[1] * arr[5] * arr[6] + arr[2] * arr[3] * arr[7] - arr[2] * arr[4] * arr[6] - arr[1] * arr[3] * arr[8] - arr[0] * arr[5] * arr[7];
    }
  
  for (i = 0; i < rows; i++) {
    for (j = 0; j < rows; j++) {
      for (k = 0; k < rows; k++) {
	for (l = 0; l < rows; l++) {
	  if (k != 0 && l != i) {
	    submatrix[k - 1][l - 1] = arr[k * rows + l];
	  }
	}
      }
      det += arr[i] * determinant((float *)submatrix, rows - 1, cols - 1) * (i % 2 == 0 ? 1 : -1);
    }
  }

  return det;
}
  

float test_13(float a, float b, float c);

float test_13_tester(float a, float b, float c)
{
  float arr[9] = {a, 0, 0, 0, b, 0, 0, 0, c};

  float d = determinant((float *)arr, 3, 3);
  //printf("det: %f\n",d);  
  
  return a/d + b/d + c/d;
}

int main()
{

  for(int i=1; i<100; i++)
    {
      float ret = test_13(i,i+1,i+2);
      float sol = test_13_tester(i,i+1,i+2);
      if ( !compare(ret,sol,0.0001) ) {
	printf("test_13 at %d should be %f, but got %f.\n",i,sol,ret);
	return 1;
      }
    }
    
  return 0;
}
