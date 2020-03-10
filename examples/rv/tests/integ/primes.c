// Copyright (c) 2019, Massachusetts Institute of Technology
//
// Author: Clément Pit-Claudel <cpitcla@csail.mit.edu>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

#include <stdbool.h>

int putchar(int c);

#define LINE_LENGTH 27
#define LINE_COUNT 13
#define OFFSET 0

// #define VERIFY

#ifdef VERIFY
char ground_truth[80 * 30] =
  "+++-+*+---+-+---+-+---+----*+-+-----+---+-+---+-----+-----+-+-----+---+-+-----+-"
  "--+-----+-------+---+-+---+-+---+-------------+---+-----+-+---------+-+-----+---"
  "--+---+-----+-----+-+---------+-+---+-+-----------+--------&--+---+-+---+-----+-"
  "+---------+-----+-----+-----+-+-----+---+-+&--------+-------------+---+-+---+---"
  "----------+-----+---------+-+---+-----+-------+-----+-----+---+-----+-------+---"
  "+-------+---------+-+---------+-+-----+---+-----+-------+---+-+---+-----------+-"
  "------+---+----*--+---+-----+-----------+-+-----------------+-----+---------+---"
  "--+-----+-+-----+---------+-----+-----+-+-----+-----+---+-+-----------+---------"
  "+-+---+-----+-----+-+-----------+---+-----+-------+---------+-------+---------+-"
  "------+-----+-----+---+-------+-----+---+-------+---+-------------+---------+---"
  "--------+-+---------+-+---+-+---------+-------------+---+-+---+-------------+---"
  "+-+---+-------------------+---+-------+---------+-------+---+-----+-----+-------"
  "------+---+-----+-----+-------+-----+-----------+---+-----+-+---------+-+-----+-"
  "--------+-+---------+-+-----+-----------------+---+-+---+-----+-----+-------+---"
  "--+-----+---------------------+-+---------+-------+---------+--&--+-----+-------"
  "+--------&--+---+-----+-----+-+-----+-----------+---------+-----------------+-+-"
  "--+-----+-+-----+---+-+---+-----------+-+-----+---------------------------------"
  "+-----+-----+-------+-----------------+---------+-------------+---+-+---+-----+-"
  "------+---+-+-----+-----------+---------+-+---+-+---+-----+-----------+---------"
  "--+-------+-----------+-----+---+-----+-------+---+-------+---+-------------+---"
  "+-----+-+---+-----+-+-----+---------+-------------------+-----+---+-+-----------"
  "------------+---+-+---------+-----------+-+---------+-------+-----+-----+-----+-"
  "----------------+-----+---+-+-----------+---------+-----------+-------+---------"
  "------+-------------+-----+---+-+---+-+---------+-----------+-----+-----+-------"
  "----------+-+---------------+-+---------------------+-----+-------+-----+---+-+-"
  "--+-------+-----+---------+-+---------+-------------+---------+-----+-----------"
  "+-+---+-+---------+-----------+-+---------------+-+-----+---+-+---------+-------"
  "+-----------------+-----------------------+---+-----+-------+---------------+-+-"
  "--+-------+---------------+-+---+-------+-----+-----+---+-----------+-+---------"
  "------------+-----+-+-----+---+-----+-------------+-----+---+-+-----+---+-----+-";
#endif

typedef unsigned int uint;

uint rem(uint n, uint m) {
  while (n >= m) {
    n = n - m;
  }
  return n;
}

uint uisqrt(uint n) {
  if (n < 2)
    return n;
  uint r = uisqrt(n >> 2) << 1;
  uint R = r + 1;
  return R * R > n ? r : R;
}

bool is_prime(uint n) {
  uint r = uisqrt(n);
  for (uint m = 2; m <= r; m++) {
    if (rem(n,m) == 0)
      return false;
  }
  return true;
}

uint aliquot(uint n) {
  uint sum = 0;
  for (uint m = 1; m < n; m++) {
    if (rem(n,m) == 0)
      sum += m;
  }
  return sum;
}

bool is_perfect(uint n) {
  return n == aliquot(n);
}

bool is_amicable(uint n) {
  uint an = aliquot(n);
  for (uint m = 1; m <= an; m++) {
    if (m == an && n == aliquot(m))
      return true;
  }
  return false;
}

int main() {
  for (uint l = 0; l < LINE_COUNT; l++) {
    putchar(' '); putchar(' ');
    for (uint c = 0; c < LINE_LENGTH; c++) {
      uint n = 1 + OFFSET + l * LINE_LENGTH + c;
      char c = ' ';
      if (is_perfect(n)) {
        c = '*';
      } else if (is_prime(n)) {
        c = '+';
      } else if (is_amicable(n)) {
        c = '&';
      } else {
        c = '-';
      }
      putchar(c);
#ifdef VERIFY
      if (c != ground_truth[n - 1])
        return 1;
#endif
    }
    putchar('\n');
  }
  return 0;
}
