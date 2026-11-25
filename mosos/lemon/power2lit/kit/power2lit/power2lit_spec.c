/* power2lit_spec.c: executable versions of the specification
   functions of the Event-B context, synthesized by eb2pcal from the axioms
   (the axiom of each case is given in a comment). They are used by the
   functions called by the algorithm and by the run-time check of the
   postcondition in main.c. */

#include <stdio.h>
#include <stdlib.h>
#include "power2lit.h"

/* v: function of the specification (logic) */
int v(int x)
{
  if (x == 0) return 0;   /* A-C0_axm6 */
  if ((0 <= x - 1)) return v(x - 1) + w(x - 1) + 1;   /* A-C0_axm7 */
  if ((0 <= x)) return x * x;   /* A-C0_th2 (theorem) */
  fprintf(stderr, "v: undefined for these arguments\n");
  exit(2);
}

/* w: function of the specification (logic) */
int w(int x)
{
  if (x == 0) return 0;   /* A-C0_axm3 */
  if ((0 <= x - 1)) return w(x - 1) + 2;   /* A-C0_axm4 */
  if ((0 <= x)) return 2 * x;   /* A-C0_th1 (theorem) */
  fprintf(stderr, "w: undefined for these arguments\n");
  exit(2);
}
