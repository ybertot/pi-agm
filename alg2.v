Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral.
Require Import elliptic_integral arcsinh generalities agmpi.
Require Import Interval.Interval_tactic.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

Print k_.

Search Derive k_.

Lemma ex_derive_ratio n x (intx : 0 < x < 1) :
  ex_derive (fun y => u_ n y / v_ n y) x.
Proof.
assert (0 < v_ n x).
  now destruct (ag_le n 1 x); unfold v_; psatzl R.
auto_derive.
destruct (ex_derive_ag n x (proj1 intx)) as [d1 [d2 [du [dv _]]]].
repeat (split;[eapply ex_intro; eassumption| ]); psatzl R.
Qed.

Lemma is_derive_k_extra n x (intx : 0 < x < 1) :
  is_derive (k_ n) x
  (- ((/ 2 ^ n * (v_ n x) ^ 3 / (u_ n x * (w_ n x) ^ 2)) * 
     Derive (fun x => u_ n x / v_ n x) x)).
Proof.
assert (help : u_ n x ^ 2 - v_ n x ^ 2 = (u_ n x + v_ n x) * (u_ n x - v_ n x)).
  ring.
evar_last;[apply is_derive_k, intx | ].
unfold Rdiv at 3; rewrite -> !Rmult_assoc, Ropp_mult_distr_r.
apply f_equal; rewrite (is_derive_unique (w_ n) x _ (is_derive_w n x intx)).
assert (0 < v_ n x /\ 0 < u_ n x).
  now destruct (ag_le n 1 x); unfold v_, u_; psatzl R.
assert (v_ n x < u_ n x) by (apply ag_lt; psatzl R).
assert (0 < w_ n x).
  unfold w_; rewrite help; lt0.
assert (dd : Derive (fun y => u_ n y / v_ n y) x =
        (Derive (u_ n) x * v_ n x - Derive (v_ n) x * u_ n x) / (v_ n x) ^ 2).
  apply is_derive_unique; auto_derive; cycle 1.
    change (Derive (fun x => u_ n x)) with (Derive (u_ n)).
    change (Derive (fun x => v_ n x)) with (Derive (v_ n)).
    field; psatzl R.
  destruct (ex_derive_ag n x (proj1 intx)) as [d1 [d2 [du [dv dup]]]].
  repeat (split;[eapply ex_intro; eassumption |]); psatzl R.
rewrite dd; clear dd; change (Derive (fun x => v_ n x)) with (Derive (v_ n)).
change (sqrt (u_ n x ^ 2 - v_ n x ^ 2)) with (w_ n x).
rewrite Rinv_Rdiv; try psatzl R.
match goal with |- ?a = _ =>
  replace a with ((- u_ n x ^ 2 * Derive (u_ n) x + u_ n x * v_ n x *
      Derive (v_ n) x + w_ n x ^ 2 *
      Derive (u_ n) x) / (u_ n x * w_ n x ^ 2)) by (field; psatzl R)
end.
rewrite (Rmult_comm (/ (u_ n x * w_ n x ^ 2))).
unfold Rdiv; rewrite -> Ropp_mult_distr_l, <- !Rmult_assoc. 
apply f_equal with (f := (fun A => A * / (u_ n x * w_ n x ^ 2))).
replace (w_ n x ^ 2) with (u_ n x ^ 2 - v_ n x ^ 2); cycle 1.
  now unfold w_; rewrite sqrt_pow_2;[reflexivity | rewrite help; lt0].
field; psatzl R.
Qed.

Lemma derive_ratio_u_v n :
  is_derive (fun x => u_ n x / v_ n x) (/sqrt 2)
   (- 2 * sqrt 2 * 2 ^ n * u_ n (/sqrt 2) * (w_ n (/sqrt 2)) ^ 2 /
        v_ n (/sqrt 2)).
Proof.
set (x := /sqrt 2).
assert (intx : 0 < x < 1) by exact ints.
assert (help : u_ n x ^ 2 - v_ n x ^ 2 = (u_ n x + v_ n x) * (u_ n x - v_ n x)).
  ring.
assert (0 < v_ n x /\ 0 < u_ n x).
  now destruct (ag_le n 1 x); unfold v_, u_; psatzl R.
assert (v_ n x < u_ n x) by (apply ag_lt; psatzl R).
assert (0 < w_ n x).
  unfold w_; rewrite help; lt0.
assert (t'' := is_derive_unique _ _ _ (is_derive_k_extra n _ intx)).
rewrite -> Derive_k in t'';[|exact ints].
apply f_equal with (f := Ropp) in t''; rewrite Ropp_involutive in t''.
apply f_equal with (f := fun u => / (/ 2 ^ n * v_ n x ^ 3 /
                         (u_ n x * w_ n x ^ 2)) * u) in
 t''; rewrite <- (Rmult_assoc _ _ (Derive _ x)), Rinv_l, Rmult_1_l in t'';
  cycle 1.
  now lt0.
evar_last;[apply Derive_correct, ex_derive_ratio, ints |].
apply eq_trans with (1 := eq_sym t'').
assert (0 < 1 - x ^ 2)
   by (replace (1 - x ^ 2) with ((1 + x) * (1 - x)) by ring; lt0).
field_simplify; try (repeat split; try lt0); cycle 1.
replace (-v_ n x ^ 3 * x ^ 3 + v_ n x ^ 3 * x) with
  (/2 * v_ n x ^ 3 * / sqrt 2); cycle 1.
  replace (x ^ 3) with (x ^ 2 * x) by ring.
  unfold x; rewrite -> inv_sqrt, sqrt_pow_2; psatzl R.
field; split; lt0.
Qed.

