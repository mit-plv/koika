// See LICENSE.riscv-tests for license details.

#include "../mmio.h"
#include "rvbench_median_dataset.h"

static int verify(int n, const volatile int* test, const int* verify) {
  // correct: return 0
  // wrong: return wrong idx + 1
  int i;
  for (i = 0; i < n; i++)
  {
    int t = test[i];
    int v = verify[i];
    if (t != v) return i+1;
  }
  return 0;
}

void median( int n, int input[], int results[] )
{
  int A, B, C, i;

  // Zero the ends
  results[0]   = 0;
  results[n-1] = 0;

  // Do the filter
  for ( i = 1; i < (n-1); i++ ) {

    A = input[i-1];
    B = input[i];
    C = input[i+1];

    if ( A < B ) {
      if ( B < C )
        results[i] = B;
      else if ( C < A )
        results[i] = A;
      else
        results[i] = C;
    }

    else {
      if ( A < C )
        results[i] = A;
      else if ( C < B )
        results[i] = B;
      else
        results[i] = C;
    }

  }

}

int main() {
	int results_data[DATA_SIZE];
	median(DATA_SIZE, input_data, results_data);
	return verify( DATA_SIZE, results_data, verify_data );
}
