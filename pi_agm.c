#include <stdio.h>

#include <gmp.h>
#include <mpfr.h>

static mpfr_t t, y, z, y1, z1, a, b, c;

void next_y_sqrt_y(void) {
  /* before: y1 = u_n + 1, y = y_n, after: y = y_{n+1}, b = sqrt(y_n), t = 1 */
  mpfr_sqrt(b, y, MPFR_RNDD);
  mpfr_mul_ui(c, b, 2, MPFR_RNDD);
  mpfr_div(y, y1, c, MPFR_RNDD);
}

void advance_product (void) {
  mpfr_add(y1, y, t, MPFR_RNDD);
  mpfr_add(z1, z, t, MPFR_RNDD);
  mpfr_div(b, y1, z1, MPFR_RNDD);
  mpfr_mul(a, a, b, MPFR_RNDD);
}

int main (void)
{
  unsigned int my_prec = 3321938; /* four extra digits. */
  
  unsigned int i;

  mpfr_init2 (t, my_prec);
  mpfr_init2 (a, my_prec);
  mpfr_init2 (b, my_prec);
  mpfr_init2 (y, my_prec);
  mpfr_init2 (y1, my_prec);
  mpfr_init2 (c, my_prec);
  mpfr_init2 (z, my_prec);
  mpfr_init2 (z1, my_prec);
  
  mpfr_set_d (t, 1.0, MPFR_RNDD);
  mpfr_set_d (a, 2.0, MPFR_RNDD);
  mpfr_sqrt(y, a, MPFR_RNDD);     /* here y is y_0 = sqrt(2) */
  mpfr_add(y1, y, t, MPFR_RNDD);  /* here y1 is y_0 + 1 */
  mpfr_add(a, a, y, MPFR_RNDD);   /* here a is pi_0 = 2 + sqrt(2) */
  mpfr_sqrt(z, y, MPFR_RNDD);    /* here z is z_1 = sqrt(sqrt(2)) */
  next_y_sqrt_y();
  advance_product(); /* Here a contains pi_1 */
  for (i = 1; i < 20; i ++) {
    mpfr_mul(z, z, y, MPFR_RNDD);
    mpfr_add(z, z, t, MPFR_RNDD);
    next_y_sqrt_y(); /* y = y_(n+1), b = sqrt(y_n) */
    mpfr_mul(z1, z1, b, MPFR_RNDD);
    mpfr_div(z, z, z1, MPFR_RNDD);  /* z = z_(n+1) */
    advance_product();
  }
  
  mpfr_out_str (stdout, 10, 0, a, MPFR_RNDD);
  putchar ('\n');
  return 0;
}




