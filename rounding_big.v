Require Import BigZ.

Definition hmult (precision x y : bigZ) := (x * y / precision)%bigZ.
Definition hdiv (precision x y : bigZ) := (x * precision / y)%bigZ.
Definition hsqrt (precision x : bigZ) := BigZ.sqrt (precision * x).
Definition h2 precision := (2 * precision)%bigZ.
Definition h1 (precision : bigZ) := precision.

Fixpoint hpi_rec (precision : bigZ)
  (n : nat) (y z prod : bigZ) {struct n} : bigZ :=
  match n with
  | 0%nat =>
      hmult precision (h2 precision + hsqrt precision (h2 precision)) prod
  | S p =>
      let sy := hsqrt precision y in
      let ny := hdiv precision (h1 precision + y) (2 * sy) in
      let nz :=
        hdiv precision (h1 precision + hmult precision y z)
          (hmult precision (h1 precision + z) sy) in
      hpi_rec precision p ny nz
        (hmult precision prod
           (hdiv precision (h1 precision + ny) (h1 precision + nz)))
  end.

Definition hs2 (precision : bigZ) :=
  hsqrt precision (h2 precision).

Definition hy1 (precision : bigZ) :=
  hdiv precision (h1 precision + hs2 precision)
  (2 * hsqrt precision (hs2 precision)).

Definition hz1 (precision : bigZ) :=
  hsqrt precision (hs2 precision).

Definition hpi (precision : bigZ) (n : nat) :=
match n with
| 0%nat =>
    (h2 precision + hsqrt precision (h2 precision))%bigZ
| S p =>
    hpi_rec precision p (hy1 precision) (hz1 precision)
      (hdiv precision (h1 precision + hy1 precision)
         (h1 precision + hz1 precision))
end.

Definition thousand_digit_pi :=
let precision := (2 ^ 3335)%bigZ in
let n := hpi precision 10 in
let n' := (n * 10 ^ (10 ^ 3 + 4) / precision)%bigZ in
let (q, r) := BigZ.div_eucl n' (10 ^ 4) in
  (((217 <? r)%bigZ && (r <? 9783)%bigZ)%bool, q).

Definition million_digit_pi :=
let precision := (2 ^ 3321942)%bigZ in
let n := hpi precision 20 in
let n' := (n * 10 ^ (10 ^ 6 + 4) / precision)%bigZ in
let (q, r) := BigZ.div_eucl n' (10 ^ 4) in
(((427 <? r)%bigZ && (r <? 9573)%bigZ)%bool, q).

(* The following line can be run in coq-8.5. *)
(* Time Eval vm_compute in thousand_digit_pi. *)
(* The following line can only be run in a version of coq
   that supports native computation. *)
(* Time Eval native_compute in  million_digit_pi. *)
