Require Import Psatz Reals Coquelicot.Coquelicot Interval.Tactic
  generalities elliptic_integral agmpi.
Require Import Bool Zwf.

From Bignums Require Import BigZ.
Require Import rounding_correct.
Require rounding_big.

Local Open Scope bigZ.

Lemma hmult_morph p x y: [rounding_big.hmult p x y] = hmult [p] [x] [y].
Proof.
unfold hmult, rounding_big.hmult.
rewrite BigZ.spec_div, BigZ.spec_mul; reflexivity.
Qed.

Lemma hdiv_morph p x y: [rounding_big.hdiv p x y] = hdiv [p] [x] [y].
Proof.
unfold hdiv, rounding_big.hdiv.
rewrite BigZ.spec_div, BigZ.spec_mul; reflexivity.
Qed.

Lemma hsqrt_morph p x: [rounding_big.hsqrt p x] = hsqrt [p] [x].
Proof.
unfold hsqrt, rounding_big.hsqrt.
rewrite BigZ.spec_sqrt, BigZ.spec_mul; reflexivity.
Qed.

Lemma h2_morph p : [rounding_big.h2 p] = h2 [p].
Proof.
unfold h2, rounding_big.h2; rewrite BigZ.spec_mul; reflexivity.
Qed.

Lemma hpi_rec_morph :
 forall s p n v1 v2 v3,
   [s] = hsqrt [p] (h2 [p]) ->
   [rounding_big.hpi_rec p n s v1 v2 v3] =
   hpi_rec [p] n [s] [v1] [v2] [v3].
Proof.
intros s p n v1 v2 v3 hs; revert v1 v2 v3.
induction n as [ | n IHn]; intros v1 v2 v3.
  simpl.
  rewrite hmult_morph, BigZ.spec_add, hs, h2_morph; reflexivity.
unfold rounding_big.hpi_rec.
change ([let sy := rounding_big.hsqrt p v1 in
          let ny := rounding_big.hdiv p (p + v1) (2 * sy) in
          let nz := rounding_big.hdiv p (p + rounding_big.hmult p v2 v1)
                       (rounding_big.hmult p (p + v2) sy) in
          rounding_big.hpi_rec p n s ny nz
             (rounding_big.hmult p v3 (rounding_big.hdiv p (p + ny) (p + nz)))] =
          let sy := hsqrt [p] [v1] in
          let ny := hdiv [p] (h1 [p] + [v1]) (2 * sy) in
          let nz := hdiv [p] (h1 [p] + hmult [p] [v2] [v1])
                       (hmult [p] (h1 [p] + [v2]) sy) in
          hpi_rec [p] n [s] ny nz
             (hmult [p] [v3] (hdiv [p] (h1 [p] + ny) (h1 [p] + nz)))).
lazy zeta; rewrite IHn; clear IHn.
 rewrite !hdiv_morph, !BigZ.spec_add, !BigZ.spec_mul, !hmult_morph, !hsqrt_morph.
 rewrite hdiv_morph, !BigZ.spec_add, !hdiv_morph, !BigZ.spec_mul, !BigZ.spec_add,
  !hmult_morph, !BigZ.spec_add, hsqrt_morph; reflexivity.
Qed.

Lemma hsyz_morph p : let '(s, y, z) := rounding_big.hsyz p in
   [s] = hsqrt [p] (h2 [p]) /\ [y] = snd (fst (hsyz [p])) /\
       [z] = snd (hsyz [p]).
Proof.
unfold rounding_big.hsyz, rounding_big.hs2, hsyz, hs2.
rewrite !hdiv_morph, !BigZ.spec_add, !BigZ.spec_mul, !hsqrt_morph, h2_morph.
repeat split; reflexivity.
Qed.

Lemma hpi_morph : forall p n, [rounding_big.hpi p n]%bigZ = hpi [p]%bigZ n.
Proof.
intros p; case n as [ | n].
  simpl.
  rewrite BigZ.spec_add, h2_morph; unfold rounding_big.hs2.
  rewrite hsqrt_morph, h2_morph; reflexivity.
unfold rounding_big.hpi.
assert (tmp := hsyz_morph p); destruct (rounding_big.hsyz p) as [[s y] z].
destruct tmp as [s_m [y_m z_m]].
rewrite hpi_rec_morph;[ | assumption].
rewrite hdiv_morph, !BigZ.spec_add, s_m, y_m, z_m.
reflexivity.
Qed.

Lemma big_compute_eq : forall (p : bigZ) (q :Z) (d1 : bigZ) (d2 : Z) n,
  [p] = q -> [d1] = d2 ->
  fst (let magnifier := p in let n := rounding_big.hpi p n in
        let n' := n * d1 / p in
        let (q, r) := BigZ.div_eucl n' (10 ^ 4) in ((427 <? r) && (r <? 9573), q)) =
  fst (let magnifier := q in let n := hpi q n in
        let n' := (n * d2 / q)%Z in
        let (q, r) := Z.div_eucl n' (10 ^ 4) in
         ((427 <? r)%Z && (r <? 9573)%Z, q)) /\
  [snd (let magnifier := p in let n := rounding_big.hpi p n in
        let n' := n * d1 / p in
        let (q, r) := BigZ.div_eucl n' (10 ^ 4) in ((427 <? r) && (r <? 9573), q))] =
  snd (let magnifier := q in let n := hpi q n in
        let n' := (n * d2 / q)%Z in
        let (q, r) := Z.div_eucl n' (10 ^ 4) in
         ((427 <? r)%Z && (r <? 9573)%Z, q)).
Proof.
intros p q d1 d2 n pq d12.
lazy zeta.
generalize (BigZ.spec_div_eucl (rounding_big.hpi p n * d1 / p) (10 ^ 4)).
rewrite BigZ.spec_div, BigZ.spec_mul, hpi_morph, d12, pq.
replace [10 ^ 4] with (10 ^ 4)%Z by reflexivity.
case (BigZ.div_eucl _ _); intros q' r'; intros divq; rewrite <- divq.
split.
 rewrite !BigZ.spec_ltb; simpl; reflexivity.
simpl; reflexivity.
Qed.

Lemma big_million_eq : fst rounding_big.million_digit_pi = fst million_digit_pi /\
  [snd rounding_big.million_digit_pi] = snd million_digit_pi.
Proof.
unfold rounding_big.million_digit_pi, million_digit_pi.
apply big_compute_eq.
 rewrite BigZ.spec_pow.
 apply f_equal; reflexivity.
rewrite BigZ.spec_pow.
apply f_equal; reflexivity.
Qed.

Lemma big_pi_osix :
  fst rounding_big.million_digit_pi = true ->
    (IZR [snd rounding_big.million_digit_pi] * Rpower 10 (-(Rpower 10 6)) < PI <
    IZR [snd rounding_big.million_digit_pi] * Rpower 10 (-(Rpower 10 6))
   + Rpower 10 (-(Rpower 10 6)))%R.
Proof.
destruct big_million_eq as [f s].
rewrite f, s.
(* replace here does not work: it triggers the humongous computation. *)
 assert (big : Rpower 10 (- Rpower 10 6) = /IZR (10 ^ 10 ^ 6)).
(* Here we need the clear tactic, otherwise, it again triggers a humongous
  computation.  I don't know why. *)
clear; rewrite Rpower_Ropp, !Zpow_Rpower; try (reflexivity || discriminate).
generalize pi_osix; unfold hR; rewrite big; intros tmp; exact tmp.
Qed.
