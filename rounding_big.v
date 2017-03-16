Require Import BigZ.

Definition hmult (magnifier x y : bigZ) := (x * y / magnifier)%bigZ.
Definition hdiv (magnifier x y : bigZ) := (x * magnifier / y)%bigZ.
Definition hsqrt (magnifier x : bigZ) := BigZ.sqrt (magnifier * x).
Definition h1 (magnifier : bigZ) := magnifier.
Definition h2 magnifier := (2 * magnifier)%bigZ.


Fixpoint hpi_rec (magnifier : bigZ)
  (n : nat) (s2 y z prod : bigZ) {struct n} : bigZ :=
  match n with
  | 0%nat =>
      hmult magnifier (h2 magnifier + s2) prod
  | S p =>
      let sy := hsqrt magnifier y in
      let ny := hdiv magnifier (h1 magnifier + y) (2 * sy) in
      let nz :=
        hdiv magnifier (h1 magnifier + hmult magnifier z y)
          (hmult magnifier (h1 magnifier + z) sy) in
      hpi_rec magnifier p s2 ny nz
        (hmult magnifier prod
           (hdiv magnifier (h1 magnifier + ny) (h1 magnifier + nz)))
  end.

Definition hs2 (magnifier : bigZ) :=
  hsqrt magnifier (h2 magnifier).

Definition hsyz (magnifier : bigZ) :=
  let hs2 := hs2 magnifier in
  let hss2 := hsqrt magnifier hs2 in
  (hs2, (hdiv magnifier (h1 magnifier + hs2) (2 * hss2)), hss2).

Definition hpi (magnifier : bigZ) (n : nat) :=
match n with
| 0%nat =>
    (h2 magnifier + (hs2 magnifier))%bigZ
| S p =>
    let '(s2, y1 , z1) := hsyz magnifier in
    hpi_rec magnifier p s2 y1 z1
      (hdiv magnifier (h1 magnifier + y1)
         (h1 magnifier + z1))
end.

Definition thousand_digit_pi :=
let magnifier := (2 ^ 3335)%bigZ in
let n := hpi magnifier 10 in
let n' := (n * 10 ^ (10 ^ 3 + 4) / magnifier)%bigZ in
let (q, r) := BigZ.div_eucl n' (10 ^ 4) in
  (((217 <? r)%bigZ && (r <? 9783)%bigZ)%bool, q).

Definition hundred_thousand_digit_pi :=
let magnifier := (2 ^ 332207)%bigZ in
let n := hpi magnifier 17 in
let n' := (n * 10 ^ (10 ^ 5 + 4) / magnifier)%bigZ in
let (q, r) := BigZ.div_eucl n' (10 ^ 4) in
  ((21 * 17 + 7 <? r)%bigZ && (r <? 10000 - (21 * 17 + 7))%bigZ, q)%bool.

Definition million_digit_pi :=
let magnifier := (2 ^ 3321942)%bigZ in
let n := hpi magnifier 20 in
let n' := (n * 10 ^ (10 ^ 6 + 4) / magnifier)%bigZ in
let (q, r) := BigZ.div_eucl n' (10 ^ 4) in
(((427 <? r)%bigZ && (r <? 9573)%bigZ)%bool, q).

(* The following line can be run in coq-8.5. *)
(* Time Eval vm_compute in thousand_digit_pi. *)
(* The following line can only be run in a version of coq
   that supports native computation. *)
(* Time Eval native_compute in  million_digit_pi. *)

Fixpoint salamin_rec (magnifier : bigZ) (n :nat) (a b am1 bm1 sum twopk : bigZ) :=
  match n with
    O%nat => hdiv magnifier (4 * hmult magnifier  a a) sum
  | S p => salamin_rec magnifier p 
            ((a + b) / 2)%bigZ (hsqrt magnifier (hmult magnifier a b)) a b
            (let v := (am1 - bm1)%bigZ in
               (sum - twopk * (hmult magnifier v v))%bigZ)
            (2 * twopk)%bigZ
  end.

Definition salamin magnifier n :=
  let s2 := hdiv magnifier magnifier (hsqrt magnifier (h2 magnifier)) in
  let a1 := ((h1 magnifier + s2) / 2)%bigZ in
  let b1 := hsqrt magnifier s2 in
  let twopk := 1%bigZ in
  salamin_rec magnifier n a1 b1 (h1 magnifier) s2 (h1 magnifier) twopk.

