# pi-agm
A formal description in Coq of computations of PI using arithmetic-geometric means

Reminder: to generate a makefile, type coq_makefile -f _CoqProject -o Makefile

To compile the C file, install the mpfr library, and then:

<pre>
cc -o pi_agm -lmpfr pi_agm.c
</pre>

# Displaying theorems in Coq

## Coq installed through opam (works with coq-8.6 and coq-8.7)

If you installed coq through opam, you can compile the whole library and
install it by typing

    opam repo add coq-released http://coq.inria.fr/opam/released
    opam install coq-interval
    opam install coq-pi-agm

You can see the main theorems by launching the <code>coqtop</code> and
typing the following commands:

    Require Import agm.hrounding_correct agm.agmpi agm.alg2 agm.rounding2.
    Import rounding_big Reals.
    Check big_pi_osix.
    Check bound_agmpi.
    Check salamin_convergence_speed'.
