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
set (x := /sqrt 2); assert (intx : 0 < x < 1) by exact ints.
assert (help : forall x y, x ^ 2 - y ^ 2 = (x + y) * (x - y)) by (intros; ring).
assert (0 < v_ n x /\ 0 < u_ n x).
  now destruct (ag_le n 1 x); unfold v_, u_; psatzl R.
assert (v_ n x < u_ n x) by (apply ag_lt; psatzl R).
assert (0 < w_ n x) by (unfold w_; rewrite help; lt0).
assert (t'' := is_derive_unique _ _ _ (is_derive_k_extra n _ intx)).
rewrite -> Derive_k in t'';[|exact ints].
apply f_equal with (f := Ropp) in t''; rewrite Ropp_involutive in t''.
apply f_equal with (f := fun u => / (/ 2 ^ n * v_ n x ^ 3 /
                         (u_ n x * w_ n x ^ 2)) * u) in t''.
rewrite <- (Rmult_assoc _ _ (Derive _ x)), Rinv_l, Rmult_1_l in t'';[| lt0].
evar_last;[apply Derive_correct, ex_derive_ratio, ints |].
apply eq_trans with (1 := eq_sym t'').
assert (0 < 1 - x ^ 2) by (rewrite <-(pow1 2), help; lt0).
field_simplify; try (repeat split; try lt0).
replace (-v_ n x ^ 3 * x ^ 3 + v_ n x ^ 3 * x) with
  (/2 * v_ n x ^ 3 * / sqrt 2);[field; split; lt0 |].
replace (x ^ 3) with (x ^ 2 * x) by ring.
unfold x; rewrite -> inv_sqrt, sqrt_pow_2; psatzl R.
Qed.

Lemma cv_ff_3_over_ff'_v :
   is_lim_seq (fun n =>
              u_ n (/sqrt 2) ^ 2 * v_ n (/sqrt 2) /
              Derive (v_ n) (/sqrt 2)) (PI / (2 * sqrt 2)).
Proof.
assert (ints := ints); set (s2 := /sqrt 2); fold s2 in ints.
  apply (is_lim_seq_ext_loc
    (fun n =>
         y_ n s2 / z_ n s2 * (v_ n s2 ^ 2 * u_ n s2 / Derive (u_ n) s2))).
  exists 1%nat; intros n n1.
  unfold y_, z_; simpl; change (fun x => v_ n x) with (v_ n); field.
  destruct (ag_le n 1 s2); try lt0.
  assert (t := ag_lt n 1 s2 ints); try lt0.
  assert (t' := compare_derive_ag n s2 n1 ints).
  now unfold u_, v_ in t' |- *; repeat split; lt0.
apply (is_lim_seq_mult _ _ 1 (PI / (2 * sqrt 2))); cycle 1.
    now apply cv_ff_3_over_ff'.
  now unfold is_Rbar_mult; simpl; rewrite Rmult_1_l.
assert (0 < ff s2).
  destruct (M_between 1 s2 1) as [mb1 mb2]; try lt0.
  now destruct (ag_le 1 1 s2); unfold ff; lt0.
apply (is_lim_seq_div _ _ 1 1);
  [ | | injection; exact R1_neq_R0 |
    now unfold is_Rbar_div, is_Rbar_mult; simpl; apply f_equal; 
    rewrite -> Rinv_1, Rmult_1_l].
  unfold y_; apply (is_lim_seq_div _ _ (ff s2) (ff s2)); cycle 3.
        unfold is_Rbar_div, is_Rbar_mult; simpl; apply f_equal.
        now rewrite Rinv_r; [reflexivity | lt0].
      now apply is_lim_seq_fst_ag.
    now apply is_lim_seq_snd_ag.
  now injection; apply Rgt_not_eq; lt0.
rewrite is_lim_seq_Reals.
Search CVU Un_cv.
assert (int: 0 < /2 < 3 /4) by (split; interval).
assert (int' : 3 / 4 < 1) by interval.
assert (d0 : 0 < /100) by interval.
set (d := mkposreal _ d0).
assert (dl : /2 < s2 - d) by (unfold s2, d; simpl; interval).
assert (du : s2 + d < 3/4) by (unfold s2, d; simpl; interval).
intros eps e0; destruct (CVU_z _ _ int int' s2 d dl du _ e0) as [N Pn].
exists N; intros n nN; rewrite R_dist_sym; apply (Pn n s2);[lia | ].
now apply Boule_center.
Qed.

Lemma diff_square x y : x ^ 2 - y ^ 2 = (x + y) * (x - y).
Proof. intros; ring. Qed.

Lemma ratio_v'_v n (n1 : (1 <= n)%nat) :
  Derive (v_ n) (/sqrt 2) / v_ n (/sqrt 2) =
  Derive (v_ 1) (/sqrt 2) / v_ 1 (/sqrt 2)  - sqrt 2 * sum_f_R0 (fun k =>
            if k =? 0  then 0
            else 2 ^ k * (u_ k (/sqrt 2) ^ 2 - v_ k (/sqrt 2) ^ 2)) (n - 1).
Proof.
assert (ints := ints); set (s2 := /sqrt 2); fold s2 in ints.
induction n1 as [| n n1 Ih].
  now simpl; rewrite -> Rmult_0_r, Rminus_0_r.
destruct n as [ | m]; [inversion n1 | clear n1; set (n := S m)].
replace (S m - 1)%nat with m in Ih by lia.
replace (S n - 1)%nat with (S m) by (unfold n; lia).
rewrite -> tech5, Rmult_plus_distr_l; simpl (S m =? 0); lazy iota.
unfold Rminus in Ih |- *; rewrite -> Ropp_plus_distr.
rewrite <- !(Rplus_assoc _ _ (-(sqrt 2 * (2 ^ _ * _)))), <- Ih; clear Ih.
assert (dvu : v_ n s2 < u_ n s2) by now apply ag_lt.
destruct (ag_le n 1 s2) as [agl1 agl2]; try psatzl R.
fold n; fold (v_ n s2) in agl1, agl2; fold (u_ n s2) in agl2.
replace (- (sqrt 2 * (2 ^ n * (u_ n s2 ^ 2 + - v_ n s2 ^ 2)))) with
  (/2 * Derive (fun x => u_ n x / v_ n x) s2 * v_ n s2/ u_ n s2); cycle 1.
  rewrite (is_derive_unique _ _ _ (derive_ratio_u_v n)).
  replace (u_ n s2 ^ 2 + - v_ n s2 ^ 2) with (w_ n s2 ^ 2); cycle 1.
    now unfold w_; rewrite sqrt_pow_2;[ |rewrite diff_square; lt0].
  fold s2; field; psatzl R.
assert (dr : Derive (fun x => u_ n x / v_ n x) s2 =
          (Derive (u_ n) s2 * v_ n s2 - Derive (v_ n) s2 * u_ n s2) /
          v_ n s2 ^ 2).
  auto_derive_fun (fun x => u_ n x / v_ n x); intros adh.
  destruct (ex_derive_ag n s2 (proj1 ints)) as [d1 [d2 ps]].
  assert (exu : ex_derive (u_ n) s2) by (exists d1; tauto).
  assert (exv : ex_derive (v_ n) s2) by (exists d2; tauto).
  assert (vn0 : v_ n s2 <> 0) by psatzl R.
  rewrite (is_derive_unique _ _ _ (adh _ (conj exu (conj exv (conj vn0 I))))).
  change (fun x => u_ n x) with (u_ n); change (fun x => v_ n x) with (v_ n).
  now field.
rewrite -> dr, derive_snd_step;[|psatzl R].
rewrite v_step; field_simplify; try (repeat split; lt0).
rewrite -> (Rmult_assoc 2), <- sqrt_mult; try (repeat split; lt0).
field_simplify; try (repeat split; lt0); rewrite sqrt_pow_2;[ | lt0].
now change (fun x => v_ n x) with (v_ n); field; lt0.
Qed.

Lemma final_formula :
  is_lim_seq 
    (fun n =>
     4 *  u_ n (/sqrt 2) ^ 2 /
     (1 - sum_f_R0 (fun k => if k =? 0  then 0
        else 2 ^ (k - 1) * ((u_ (k - 1) (/sqrt 2) - v_ (k - 1) (/sqrt 2))) ^ 2)
               (n - 1)))
    PI.
Proof.
apply (is_lim_seq_ext_loc
  (fun n => (2 * sqrt 2) * (u_ n (/sqrt 2) ^ 2 * v_ n (/sqrt 2) /
                            Derive (v_ n) (/sqrt 2)))); cycle 1.
  replace PI with ((2 * sqrt 2) * (PI / (2 * sqrt 2))) by (field; lt0).
  apply (is_lim_seq_mult _ _ (2 * sqrt 2) (PI / (2 * sqrt 2))).
      now apply is_lim_seq_const.
    now apply cv_ff_3_over_ff'_v.
  reflexivity.
exists 1%nat; intros n n1.
assert (dvu : v_ n (/sqrt 2) < u_ n (/sqrt 2)) by (apply ag_lt; exact ints).
assert (t := ints).
destruct (ag_le n 1 (/sqrt 2)) as [agl1 agl2]; try (psatzl R).
fold (u_ n (/sqrt 2)) in *.
fold (v_ n (/sqrt 2)) in *.
set (s2 := /sqrt 2); fold s2 in dvu, t, agl1, agl2 |- *.
replace (2 * sqrt 2 * (u_ n s2 ^ 2 * v_ n s2 / Derive (v_ n) s2)) with
   (4 * u_ n s2 ^ 2 / (sqrt 2 * (Derive (v_ n) s2 / v_ n s2))); cycle 1.
  replace 4 with (2 * (sqrt 2 * sqrt 2)) by (rewrite sqrt_sqrt; psatzl R).
  field; repeat split; try lt0.
  destruct (compare_derive_ag n s2 n1 ints) as [cd1 cd2].
  change (fun x => v_ n x) with (v_ n) in cd2; lt0.
apply (f_equal (fun x => 4 * u_ n s2 ^ 2 / x)).
rewrite (sum_eq _ (fun k => 
                      (if k =? 0 then 0 else
                           2 ^ k * (u_ k s2 ^ 2 - v_ k s2 ^ 2)) * 2)); cycle 1.
  intros [ | i] _; simpl;[now rewrite Rmult_0_l | ].
  rewrite -> Nat.sub_0_r, u_step, v_step, !Rmult_1_r, sqrt_sqrt;[field | ].
  now destruct (ag_le i 1 s2) as [agi1 agi2]; unfold u_, v_; lt0. 
rewrite <- scal_sum; rewrite ratio_v'_v; auto.
assert (sqrt_manip : forall a, 1 - 2 * a = sqrt 2 * (/sqrt 2 - sqrt 2 * a)).
  intros a; rewrite -> Rmult_minus_distr_l, Rinv_r, <- Rmult_assoc, sqrt_sqrt;
    lt0.
assert (hd : Derive (v_ 1) s2 / v_ 1 s2 = /sqrt 2).
  rewrite derive_snd_step;[|psatzl R].
  unfold u_, v_; simpl; rewrite -> Derive_const, Derive_id, Rmult_0_l, Rplus_0_l.
  rewrite -> sqrt_1, !Rmult_1_l.
  unfold s2; field_simplify;[ | interval | repeat split; interval].
  rewrite sqrt_pow_2;[|lt0].
  replace 2 with (sqrt 2 * sqrt 2) at 1 by (rewrite sqrt_sqrt; psatzl R).
  field; lt0.
(* Here I need to use the ssreflect rewrite. *)
rewrite hd; rewrite sqrt_manip; reflexivity.
Qed.
