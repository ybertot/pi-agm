# pi-agm
A formal description in Coq of computations of PI using arithmetic-geometric means

Reminder: to generate a makefile, type coq_makefile -f _CoqProject -o Makefile

To compile the C file, install the mpfr library, and then:

<pre>
cc -o pi_agm -lmpfr pi_agm.c
</pre>