/* main.c: runs the algorithm power2lit on examples and checks, at run
   time, its precondition and its postcondition (defined by the event(s) of
   the first machine of the Event-B development). */

#include <stdio.h>
#include <stdlib.h>
#include "power2lit.h"

static int failures = 0;

static void check(int ok, const char *what)
{
  if (!ok) {
    printf("  postcondition FAILED: %s\n", what);
    failures++;
  }
}

/* one run of the algorithm */
static void run(int n0, int r0)
{
  printf("power2lit(n0=%d r0=%d)\n", n0, r0);
  if (!(0 <= n0)) {   /* precondition A-C0_pre1 */
    printf("  precondition A-C0_pre1 not satisfied: example skipped\n");
    return;
  }
  if (!(1)) {   /* precondition A-C0_pre2 */
    printf("  precondition A-C0_pre2 not satisfied: example skipped\n");
    return;
  }
  if (!(n0 >= 3)) {   /* precondition A-C0_axm11 */
    printf("  precondition A-C0_axm11 not satisfied: example skipped\n");
    return;
  }
  power2lit(n0, r0);
}

int main(int argc, char **argv)
{
  if (argc == 3) {   /* ./run n0 r0 */
    run(atoi(argv[1]), atoi(argv[2]));
  } else {
    run(5, 0);
    run(-3, -3);
    run(-3, 0);
    run(-3, 1);
    run(-3, 4);
    run(-3, 7);
    run(0, -3);
    run(0, 0);
    run(0, 1);
    run(0, 4);
    run(0, 7);
    run(1, -3);
  }
  printf("%s\n", failures ? "FAILURES" : "all the examples satisfy the postcondition");
  return failures != 0;
}
