# pi-agm
A formal description in Coq of computations of PI using arithmetic-geometric means

To compile the coq code (assuming you have coq and all the required
 dependencies)

    coq_makefile -f _CoqProject -o Makefile
    make


To compile the C file, install the mpfr library, and then:

<pre>
cc -o pi_agm -lmpfr pi_agm.c
</pre>

# Displaying theorems in Coq

## Coq installed through opam (last checked with coq 8.12 and interval 4.0)

If you installed coq through opam, you can compile the whole library and
install it by typing

    opam repo add coq-released http://coq.inria.fr/opam/released
    opam install coq-pi-agm

If you want to compile your own copy of the files, you can perform the
following actions

    opam repo add coq-released http://coq.inria.fr/opam/released
    opam install coq-interval
    coq_makefile -f _CoqProject -o Makefile
    make

You can see the main theorems by launching the <code>coqtop</code> program and
typing the following commands:

    Require Import agm.hrounding_correct agm.agmpi agm.alg2 agm.rounding2.
    Import rounding_big Reals.
    Check big_pi_osix.
    Check bound_agmpi.
    Check salamin_convergence_speed'.
