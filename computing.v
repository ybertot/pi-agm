Require Import rounding_big.

Time Eval vm_compute in thousand_digit_pi.
(* Uncomment the next line for the really big computation. Use a version
  of coq where native_compute works. *)
(* Time Eval native_compute in  million_digit_pi. *)
