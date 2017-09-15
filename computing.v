Require Import Interval.BigNumsCompat rounding_big.

Eval vm_compute in hpi (10 ^ 1000) 10.

(* Uncomment the next line for the really big computation. Use a version
  of coq where native_compute works. *)
(* Time Eval native_compute in  million_digit_pi. *)
(* Time Eval vm_compute in (salamin (10 ^ 100) 6 - hpi (10 ^ 100) 6)%bigZ. *)
