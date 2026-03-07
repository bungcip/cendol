// TEST: EXEC
// CATEGORY: Execution
// STANDARD: C11
// EXPECT_STDOUT:
// 1
// 1
// 1
// 1
// 1
// 1

#include <stdio.h>

int main(void) {
  struct S {
    _Bool b: 1;
  } s;

  s.b = 1;
  printf("%d\n", s.b++);
  printf("%d\n", s.b++);
  printf("%d\n", s.b++);

  _Bool b2 = 1;
  printf("%d\n", b2++);
  printf("%d\n", b2++);
  printf("%d\n", b2++);
  return 0;
}
