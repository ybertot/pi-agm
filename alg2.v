Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral arcsinh.
Require Import elliptic_integral generalities agmpi rounding_big.
Require Import Interval.Interval_tactic.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

Lemma ex_derive_ratio n x (intx : 0 < x < 1) :
  ex_derive (fun y => u_ n y / v_ n y) x.
Proof.
assert (0 < v_ n x).
  now destruct (ag_le n 1 x); unfold v_; psatzl R.
(* TODO: in this version you cannot load rounding_correct, because it
   leads to auto_derive taking forever here. Please report bug.*)
auto_derive.
destruct (ex_derive_ag n x (proj1 intx)) as [d1 [d2 [du [dv _]]]].
repeat (split;[eapply ex_intro; eassumption| ]); psatzl R.
Qed.

(* This is equation 42 in submitted version of "distant decimals of pi" *)
Lemma is_derive_k_extra n x (intx : 0 < x < 1) :
  is_derive (k_ n) x
  (- ((/ 2 ^ n * (v_ n x) ^ 3 / (u_ n x * (w_ n x) ^ 2)) * 
     Derive (fun x => u_ n x / v_ n x) x)).
Proof.
evar_last;[apply is_derive_k, intx | ].
unfold Rdiv at 3; rewrite -> !Rmult_assoc, Ropp_mult_distr_r.
apply f_equal; rewrite (is_derive_unique (w_ n) x _ (is_derive_w n x intx)).
assert (0 < v_ n x < u_ n x) by now apply v_lt_u.
assert (0 < w_ n x) by now unfold w_; rewrite diff_square; lt0.
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
  now unfold w_; rewrite sqrt_pow_2;[reflexivity | rewrite diff_square; lt0].
field; psatzl R.
Qed.

(* This is equation 43 in submitted version of "distant decimals of pi" *)
Lemma derive_ratio_u_v n :
  is_derive (fun x => u_ n x / v_ n x) (/sqrt 2)
   (- 2 * sqrt 2 * 2 ^ n * u_ n (/sqrt 2) * (w_ n (/sqrt 2)) ^ 2 /
        v_ n (/sqrt 2)).
Proof.
set (x := /sqrt 2); assert (intx : 0 < x < 1) by exact ints.
assert (0 < v_ n x /\ 0 < u_ n x).
  now destruct (ag_le n 1 x); unfold v_, u_; psatzl R.
assert (v_ n x < u_ n x) by now apply v_lt_u.
assert (0 < w_ n x) by (unfold w_; rewrite diff_square; lt0).
assert (t'' := is_derive_unique _ _ _ (is_derive_k_extra n _ intx)).
rewrite -> Derive_k in t'';[|exact ints].
apply f_equal with (f := Ropp) in t''; rewrite Ropp_involutive in t''.
apply f_equal with (f := fun u => / (/ 2 ^ n * v_ n x ^ 3 /
                         (u_ n x * w_ n x ^ 2)) * u) in t''.
rewrite <- (Rmult_assoc _ _ (Derive _ x)), Rinv_l, Rmult_1_l in t'';[| lt0].
evar_last;[apply Derive_correct, ex_derive_ratio, ints |].
apply eq_trans with (1 := eq_sym t'').
assert (0 < 1 - x ^ 2) by (rewrite <-(pow1 2), diff_square; lt0).
field_simplify; try (repeat split; try lt0).
replace (-v_ n x ^ 3 * x ^ 3 + v_ n x ^ 3 * x) with
  (/2 * v_ n x ^ 3 * / sqrt 2);[field; split; lt0 |].
replace (x ^ 3) with (x ^ 2 * x) by ring.
unfold x; rewrite -> inv_sqrt, sqrt_pow_2; psatzl R.
Qed.

(* This is equation 49 in submitted version of "distant decimals of pi" *)
Lemma u2v_over_v'_v2u_over_u'_yz n (n1 : (1 <= n)%nat) x (intx : 0 < x < 1) :
  u_ n x ^ 2 * v_ n x / Derive (v_ n) x =
  y_ n x / z_ n x * (v_ n x ^ 2 * u_ n x / Derive (u_ n) x).
Proof.
unfold y_, z_; simpl; change (fun x => v_ n x) with (v_ n); field.
assert (t := v_lt_u _ n intx).
assert (t' := compare_derive_ag n x n1 intx).
now repeat split; lt0.
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
  now exists 1%nat; intros n n1; symmetry; apply u2v_over_v'_v2u_over_u'_yz.
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

Lemma ratio_v1'_v1 :
  Derive (v_ 1) (/sqrt 2) / v_ 1 (/sqrt 2) = / sqrt 2.
Proof.
assert (ints := ints).
rewrite derive_snd_step;[|psatzl R].
unfold u_, v_; simpl; rewrite -> Derive_const, Derive_id, Rmult_0_l, Rplus_0_l.
rewrite -> sqrt_1, !Rmult_1_l.
field_simplify;[ | interval | repeat split; interval].
rewrite sqrt_pow_2;[|lt0].
replace 2 with (sqrt 2 * sqrt 2) at 1 by (rewrite sqrt_sqrt; psatzl R).
now field; lt0.
Qed.

Definition direct_sumand k :=
   if k =? 0 then 0
   else 2 ^ k * (u_ k (/sqrt 2) ^ 2 - v_ k (/sqrt 2) ^ 2).

(* This is equation 46 in submitted version of "distant decimals of pi" *)
Lemma ratio_v'_v n (n1 : (1 <= n)%nat) :
  Derive (v_ n) (/sqrt 2) / v_ n (/sqrt 2) =
  Derive (v_ 1) (/sqrt 2) / v_ 1 (/sqrt 2)  -
        sqrt 2 * sum_f_R0 direct_sumand (n - 1).
Proof.
assert (ints := ints); set (s2 := /sqrt 2); fold s2 in ints.
induction n1 as [| n n1 Ih].
  now simpl; rewrite -> Rmult_0_r, Rminus_0_r.
(* This is equation 45 in submitted version of "distant decimals of pi" *)
destruct n as [ | m]; [inversion n1 | clear n1; set (n := S m)].
replace (S m - 1)%nat with m in Ih by lia.
replace (S n - 1)%nat with (S m) by (unfold n; lia).
rewrite -> tech5; unfold direct_sumand at 2.
rewrite -> Rmult_plus_distr_l. simpl (S m =? 0); lazy iota.
unfold Rminus in Ih |- *; rewrite -> Ropp_plus_distr.
rewrite <- !(Rplus_assoc _ _ (-(sqrt 2 * (2 ^ _ * _)))), <- Ih; clear Ih.
assert (dvu : v_ n s2 < u_ n s2) by now apply v_lt_u.
destruct (ag_le n 1 s2) as [agl1 agl2]; try psatzl R.
fold n; fold s2; fold (v_ n s2) in agl1, agl2; fold (u_ n s2) in agl2.
(* This is equation 44 in submitted version of "distant decimals of pi" *)
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
rewrite -> v_step; field_simplify; try (repeat split; lt0).
rewrite -> (Rmult_assoc 2), <- sqrt_mult; try (repeat split; lt0).
field_simplify; try (repeat split; lt0); rewrite sqrt_pow_2;[ | lt0].
now change (fun x => v_ n x) with (v_ n); field; lt0.
Qed.

Definition salamin_sumand k :=
  if k =? 0 then
    0
  else 2 ^ (k - 1) * ((u_ (k - 1) (/sqrt 2)) - v_ (k - 1) (/sqrt 2)) ^ 2.

(* This is definition 47 in submitted version of "distant decimals of pi" *)
Definition salamin_formula n :=
  4 * u_ n (/sqrt 2) ^ 2 / (1 - sum_f_R0 salamin_sumand (n - 1)).

Lemma direct_sum_0 n :
  0 < /sqrt 2 - sqrt 2 * sum_f_R0 direct_sumand n.
Proof.
assert (ints := ints); assert (n1 : (1 <= S n)%nat) by lia.
assert (t := ratio_v'_v (S n) n1); revert t.
rewrite ratio_v1'_v1; simpl; rewrite Nat.sub_0_r; intros <-.
destruct (compare_derive_ag _ (/sqrt 2) n1 ints) as [cd1 cd2].
destruct (ag_le (S n) 1 (/sqrt 2)) as [agl1 agl2]; try (psatzl R).
fold (u_ (S n) (/sqrt 2)) in *.
fold (v_ (S n) (/sqrt 2)) in *.
change (fun x => v_ (S n) x) with (v_ (S n)) in cd2.
lt0.
Qed.

Lemma direct_to_salamin n :
  2 * sqrt 2 * u_ n (/sqrt 2) ^ 2 /
   (/sqrt 2 - sqrt 2 * sum_f_R0 direct_sumand (n - 1)) =
  salamin_formula n.
Proof.
assert (ints := ints).
unfold Rdiv; replace (/ (/sqrt 2 - sqrt 2 * sum_f_R0 direct_sumand (n - 1)))
 with (sqrt 2 /
          (sqrt 2 * (/sqrt 2 - sqrt 2 * sum_f_R0 direct_sumand (n - 1))));
  cycle 1.
  unfold Rdiv; rewrite -> Rinv_mult_distr, <- Rmult_assoc; try lt0; cycle 1.
    now apply Rgt_not_eq, direct_sum_0.
  now rewrite -> Rinv_r, Rmult_1_l;[ | lt0].
unfold Rdiv; rewrite <- !Rmult_assoc, !(Rmult_assoc (2 * sqrt 2)).
unfold Rdiv; rewrite (Rmult_comm (u_ n (/sqrt 2) ^ 2) (sqrt 2)).
rewrite -> (Rmult_assoc _ (sqrt 2)), (Rmult_assoc (sqrt 2) (_ ^ 2)). 
rewrite <- (Rmult_assoc (sqrt 2) (sqrt 2)), sqrt_sqrt;[ | lt0].
rewrite <- !Rmult_assoc; unfold salamin_formula, Rdiv.
apply (f_equal (fun x => 4 * u_ n (/sqrt 2) ^ 2 / x)).
rewrite -> Rmult_minus_distr_l, Rinv_r;[| lt0].
apply f_equal; rewrite <-Rmult_assoc, sqrt_sqrt;[|lt0].
rewrite scal_sum; apply sum_eq; intros i _.
unfold direct_sumand, salamin_sumand.
destruct i as [|i];[rewrite Rmult_0_l; easy | simpl (S i =? 0); lazy iota].
simpl (S i - 1)%nat; simpl (2 ^ (S i)).
(* This is equation 36 in submitted version of "distant decimals of pi" *)
rewrite -> Nat.sub_0_r, u_step, v_step, pow2_sqrt.
  field.
now destruct (ag_le i 1 (/sqrt 2)) as [agi1 agi2]; unfold u_, v_; lt0.
Qed.

(* This is equation 48 in submitted version of "distant decimals of pi" *)
Lemma lim_salamin : is_lim_seq salamin_formula PI.
Proof.
apply (is_lim_seq_ext_loc
  (fun n => (2 * sqrt 2) * (u_ n (/sqrt 2) ^ 2 * v_ n (/sqrt 2) /
                            Derive (v_ n) (/sqrt 2)))); cycle 1.
  replace PI with ((2 * sqrt 2) * (PI / (2 * sqrt 2))) by (field; lt0).
  apply (is_lim_seq_mult _ _ (2 * sqrt 2) (PI / (2 * sqrt 2))).
      now apply is_lim_seq_const.
    now apply cv_ff_3_over_ff'_v.
  reflexivity.
exists 1%nat; intros n n1; rewrite <- direct_to_salamin.
rewrite <- ratio_v1'_v1 at 5; rewrite <- ratio_v'_v; auto.
field.
assert (t := ints).
destruct (ag_le n 1 (/sqrt 2)) as [agl1 agl2]; try (psatzl R).
fold (u_ n (/sqrt 2)) in *.
fold (v_ n (/sqrt 2)) in *.
destruct (compare_derive_ag n _ n1 ints) as [cd1 cd2].
change (fun x => v_ n x) with (v_ n) in cd2; lt0.
Qed.

Lemma ratio_v'_v_lb n (n1:  (1 <= n)%nat) :
     /2 < Derive (v_ n) (/sqrt 2) / v_ n (/sqrt 2).
Proof.
assert (ints := ints); assert (vltu := v_lt_u _ n ints).
assert (vltu' := v_lt_u _ 1 ints).
destruct (compare_derive_ag n _ n1 ints) as [du0 dultdv].
assert (un0 : u_ n (/sqrt 2) <= u_ 1 (/sqrt 2)).
  now unfold u_; apply fst_ag_decrease; try lia; try lt0.
apply Rlt_le_trans with (Derive (u_ 1) (/sqrt 2) / u_ 1 (/sqrt 2)).
  rewrite derive_fst_step; unfold u_; simpl; auto.
  now rewrite -> Derive_id, Derive_const; interval.
apply Rle_trans with (Derive (u_ n) (/sqrt 2) / u_ 1 (/sqrt 2)).
  apply Rmult_le_compat_r;[lt0 | ].
  replace n with (1 + (n - 1))%nat by lia.
  now apply derive_un_growing'.
apply Rle_trans with (Derive (v_ n) (/sqrt 2) / u_ 1 (/sqrt 2)).
  now apply Rmult_le_compat_r;[lt0 | apply Rlt_le].
apply Rmult_le_compat_l;[apply Rle_trans with (2 := Rlt_le _ _ dultdv); lt0 |].
now apply Rle_Rinv; lt0.
Qed.
    
Lemma u_n_m_v_n_bound n : 0 < u_ (n + 1) (/sqrt 2) - v_ (n + 1) (/sqrt 2) <=
  7 * Rpower 531 (- 2 ^ n).
Proof.
split; [assert (t := v_lt_u _ (n + 1) ints); lt0 | ].
set (v := v_ _ _); assert (v0 := v_lt_u _ (n + 1) ints : 0 < v < u_ _ _).
assert (v67: v < 6 / 7).
  apply Rlt_trans with (1 := proj2 v0).
  clear -n; induction n.
    now unfold u_; simpl; interval.
  now simpl; rewrite u_step; destruct (v_lt_u _ (n + 1) ints); lt0.
replace (_ - _) with (v * (y_ (n + 1) (/sqrt 2) - 1)); cycle 1.
  now unfold y_, v; field; fold v; lt0.
assert (t := majoration_y_n_vs2 n).
eapply Rle_trans;[eapply Rmult_le_compat_r;[lt0 | eapply Rlt_le, v67] | ].
apply Rle_trans with (6/7 * (8 * Rpower 531 (- 2 ^ n))).
  now apply Rmult_le_compat_l; lt0.
now rewrite <- Rmult_assoc; apply Rmult_le_compat_r; lt0.
Qed.

Lemma salamin_sum_ub  n : sum_f_R0 salamin_sumand n < /10.
Proof.
enough (main : sum_f_R0 salamin_sumand n <
           /11 * sum_f_R0 (fun x => (/11) ^ x) (n - 1)).
  apply Rlt_le_trans with (1 := main).
  rewrite tech3;[ | lt0].
  assert (0 < (/11) ^ S ( n - 1)) by lt0.
  assert ((/11) ^ S (n - 1) < 1).
    rewrite -[X in _ < X] (pow1 (S (n - 1))).
    simpl; apply Rlt_le_trans with (1 * (/11) ^ (n - 1)).
      apply Rmult_lt_compat_r; lt0.
    now apply Rmult_le_compat_l;[lt0 | apply pow_incr; lt0].
  apply Rle_trans with (/11 * ((1 - 0) / (1 - /11))).
    apply Rmult_le_compat_l;[lt0 | ].
    apply Rmult_le_compat_r;[lt0 | ].
    now apply Rplus_le_compat_l, Ropp_le_contravar; lt0.
  now apply Req_le; field.
induction n as [ | n IHn].
  now unfold salamin_sumand; simpl; lt0.
rewrite tech5; unfold salamin_sumand at 2; simpl (S n =? 0); lazy iota.
simpl (S n - 1)%nat; rewrite Nat.sub_0_r.
destruct n as [ | n].
  simpl; unfold salamin_sumand; simpl.
  now unfold u_, v_; simpl; interval.
apply Rlt_le_trans with
 (/ 11 * sum_f_R0 (fun x => (/11) ^ x) (S n - 1) +
 2^ S n * (u_ (S n) (/sqrt 2) - v_ (S n) (/ sqrt 2)) ^ 2).
  apply Rplus_lt_compat_r; assumption.
rewrite tech5; simpl (S n - 1)%nat; rewrite Nat.sub_0_r.
rewrite (Rmult_plus_distr_l _ _ ((/11) ^ S n)).
apply Rplus_le_compat_l; replace (S n) with (n + 1)%nat by ring.
assert (tmp := u_n_m_v_n_bound n).
apply Rle_trans with (2 ^ (n + 1) * (7 * Rpower 531 (-2 ^ n)) ^ 2).
  now apply Rmult_le_compat_l;[| apply pow_incr]; lt0.
rewrite Rpow_mult_distr.
rewrite <- (Rpower_pow 2 (Rpower _ _)); try lt0.
rewrite Rpower_mult; replace (INR 2) with 2 by (simpl; ring).
replace (- 2 ^ n * 2) with (- (2 ^ (n + 1))) by now rewrite pow_add; simpl; ring.
apply Rle_trans with
  (2 ^ (n + 1) * (7 ^ 2 * Rpower 531 (-INR (2 * (n + 1))))).
  repeat apply Rmult_le_compat_l; try lt0.
  rewrite !Rpower_Ropp; apply Rinv_le_contravar. 
    now unfold Rpower; lt0.
  apply Rle_Rpower; try lt0.
    now apply pos_INR.
  rewrite mult_INR; simpl INR.
  clear; induction n as [|n IHn].
    now simpl; lt0.
  simpl Nat.add; rewrite S_INR; simpl.
  apply Rmult_le_compat_l;[lt0 | ].
  apply Rle_trans with (2 := IHn); rewrite plus_INR; simpl INR.
  now assert (t := pos_INR n); lt0.
rewrite -> Rpower_Ropp, Rpower_pow; try lt0.
rewrite -> pow_mult, (Rmult_comm (2 ^ _)), Rmult_assoc. 
rewrite Rinv_pow; try lt0.
rewrite <- Rpow_mult_distr.
rewrite -> Nat.add_comm, !pow_add.
rewrite <- (Rmult_assoc (7 ^ 2)), <- (Rmult_assoc (/11)).
apply Rmult_le_compat; try lt0.
  now interval.
now apply pow_incr; interval.
Qed.

(* This is equation 50 in submitted version of "distant decimals of pi" *)
Lemma salamin_convergence_speed n (n2 : (2 <= n)%nat) :
  Rabs (salamin_formula (n + 1) - PI) <= 68 * Rpower 531 (-2 ^ (n - 1)).
Proof.
set (s2 := /sqrt 2).
assert (n1 : (1 <= n - 1)%nat) by lia.
assert (n1' : (1 <= n + 1)%nat) by lia.
assert (ints2 : 0 < s2 < 1) by exact ints.
assert (nm1p1 : (n - 1 + 1)%nat = n) by lia.
assert (t := compare_derive_ag _ s2 n1' ints2).
assert (t' := ag_le (n + 1) 1 s2 Rlt_0_1 (proj1 ints2) (Rlt_le _ _ (proj2 ints2))).
fold (v_ (n + 1) s2) in t'; change (fun x => v_ (n + 1) x) with (v_ (n + 1)) in t.
fold (u_ (n + 1) s2) in t'.
rewrite <- direct_to_salamin; rewrite <- ratio_v1'_v1 at 2.
rewrite <- ratio_v'_v; auto.
replace (2 * sqrt 2 *
          u_ (n + 1) (/sqrt 2) ^ 2 / (Derive (v_ (n + 1)) (/sqrt 2) /
          v_ (n + 1) (/sqrt 2))) with
  (2 * sqrt 2 * (u_ (n + 1) s2 ^ 2 * v_ (n + 1) s2 /
         Derive (v_ (n + 1)) s2)) by now unfold s2 in *; field; lt0.
rewrite -> u2v_over_v'_v2u_over_u'_yz; auto.
rewrite <- (Rmult_assoc (2 * sqrt 2)), (Rmult_comm (2 * sqrt 2)).
rewrite (Rmult_assoc (y_ (n + 1) s2 / z_ (n + 1) s2)).
replace 68 with (54 + 14) by ring; rewrite (Rmult_plus_distr_r 54).
replace (y_ (n + 1) s2 / z_ (n + 1) s2) with
   (y_ (n + 1) s2 / z_ (n + 1) s2 - 1 + 1) by ring.
rewrite (Rmult_plus_distr_r _ 1).
unfold Rminus at 1; rewrite Rplus_assoc.
apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat; cycle 1.
  rewrite Rmult_1_l.
  apply Rle_trans with (4 * agmpi 0 * Rpower 531 (- 2 ^ (n - 1))).
    rewrite <- agmpi_ff_3_ff'.
    assert (t'' :=  bound_agmpi (n - 1) n1).
    now rewrite nm1p1 in t''; rewrite Rabs_right; lt0.
  apply Rmult_le_compat_r;[unfold Rpower; apply Rlt_le, exp_pos|].
  rewrite -> agmpi0, derive_fst_step; unfold u_, v_; simpl; auto.
  now rewrite ->Derive_const, Derive_id; interval.
replace 54 with (3 * (1 ^2 * 1 * 2) * 9) by ring; rewrite (Rmult_assoc (3 * _)).
rewrite -> (Rmult_comm (_ - _)), Rabs_mult.
apply Rmult_le_compat; try lt0.
  rewrite Rabs_mult; apply Rmult_le_compat; try lt0.
    now interval.
  rewrite Rabs_div; try lt0.
  unfold Rdiv; apply Rmult_le_compat; try lt0.
      now rewrite Rabs_right; lt0.
    rewrite Rabs_mult; rewrite !Rabs_right; try lt0.
      apply Rmult_le_compat; try lt0.
      now apply pow_incr; lt0.
    now apply Rle_ge, pow_le; lt0.
  rewrite Rabs_right; try lt0.
  rewrite -> Nat.add_comm, <- (Rinv_involutive 2);[|lt0].
  apply Rinv_le_contravar;[lt0 |].
  apply Rle_trans with (2 := derive_un_growing' 1 n s2 ints2).
  apply Req_le; rewrite derive_fst_step; unfold u_; simpl;[|exact ints2].
  now rewrite -> Derive_const, Derive_id; field.
assert (t'' := z_gt_1 s2 _ ints2 n1').
replace (y_ (n + 1) s2 / z_ (n + 1) s2 - 1) with
  (/ z_ (n + 1) s2  *(y_ (n + 1) s2 - 1) +
       (/z_ (n + 1) s2 * (1 - z_ (n + 1) s2))); cycle 1.
  now field; apply Rgt_not_eq, Rlt_gt; lt0.
replace 9 with (1 + (1 * 8)) at 1 by ring; rewrite Rmult_plus_distr_r.
rewrite (Rmult_assoc 1).
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
  rewrite Rabs_mult; apply Rmult_le_compat; try lt0.
    rewrite Rabs_right;[ | apply Rle_ge; lt0].
    rewrite <- (Rinv_involutive 1); try lt0.
    now apply Rinv_le_contravar; lt0.
  rewrite Rabs_right; cycle 1.
    now assert (t3 := y_gt_1 s2 (n + 1) ints2); lt0.
  apply Rle_trans with (1 := proj2 (majoration_y_n_vs2 n)).
  replace n with (S (n - 1)) at 1 by lia.
  rewrite <- tech_pow_Rmult, Ropp_mult_distr_r, <- Rpower_mult.
  (* This part of the proof is unsatisfactory, using wrong constants. *)
  apply Rmult_le_reg_r with (Rpower (Rpower 531 2) (2 ^ ( n - 1))).
    now unfold Rpower; apply exp_pos.
  rewrite -> Rmult_assoc, <- Rpower_plus, Rplus_opp_l, Rpower_O;
  [|unfold Rpower; apply exp_pos].
  unfold Rpower at 1; rewrite <- Ropp_mult_distr_l, -> Ropp_mult_distr_r.
  rewrite <- ln_Rinv; try lt0.
  change (exp (2 ^ (n - 1) * ln (/ 531))) with (Rpower (/531) (2 ^ (n - 1))).
  rewrite Rpower_mult_distr; try (unfold Rpower; lt0).
  rewrite <- (Rpower_1 531) at 1;try lt0;  rewrite <- Rpower_Ropp; try lt0.
  rewrite <- Rpower_plus; replace (-(1) + 2) with 1 by ring.
  rewrite Rpower_1; try lt0.
  apply Rle_trans with (Rpower 531 1);[ unfold Rpower; interval | ].
  now apply Rle_Rpower; try lt0; apply pow_R1_Rle; lt0.
(* end of questionable part. *)
assert (n1'' : (1 <= n)%nat) by lia.
assert (t3 := chain_y_z_y s2 n ints n1'').
rewrite Rabs_mult; apply Rmult_le_compat; try lt0.
  rewrite Rabs_right;[|apply Rle_ge, Rlt_le, Rinv_0_lt_compat; lt0].
  now rewrite <- (Rinv_involutive 1); try lt0; apply Rinv_le_contravar; lt0.
rewrite -> Rabs_left1, Ropp_minus_distr; try lt0.
apply Rle_trans with (y_ n s2 - 1).
  apply Rplus_le_compat_r.
  apply Rle_trans with (1 := proj2 t3).
  assert (t4 := y_gt_1 s2 n ints2).
  now apply Rlt_le, sqrt_less; lt0.
replace n with (n - 1 + 1)%nat at 1 by lia.
apply majoration_y_n_vs2.
Qed.

(* If we want, the constants can probably be improved, as we over estimate
  v_ n with 1, when we could use 6/7 instead. *)
Lemma salamin_convergence_speed' n (n1 : (1 <= n)%nat) :
  Rabs (salamin_formula (n + 1) - PI) <= 
   (132 + 384 * 2 ^ n) * Rpower 531 (-(2 ^ n)).
Proof.
assert (help1 : forall a b c, b - c = a - c + (b - a)) by now intros; ring.
rewrite (help1 (salamin_formula (n + 2))).
apply Rle_trans with (1 := Rabs_triang _ _).
replace (132 + 384 * 2 ^ n) with
   (68 + (4 * 2 * 8 + 3 * (2 * (2 ^ n * (1 ^ 2 * 64)))))
   by ring.
rewrite !(Rmult_plus_distr_r _ _ (Rpower _ _)).
assert (n2m : (n + 2 - 1 = n + 1)%nat) by lia.
assert (n1m : (n + 1 - 1 = n)%nat) by lia.
assert (n1s : (n + 1 = S n)%nat) by ring.
apply Rplus_le_compat.
  replace (n + 2)%nat with ((n + 1) + 1)%nat by ring.
  replace n with ((n + 1) - 1)%nat at 2 by lia.
  now apply salamin_convergence_speed; lia.
assert (denpos : forall n, 0 < 1 - sum_f_R0 salamin_sumand n).
  now intros m; assert (tmp := salamin_sum_ub m); lt0.
assert (denn0 : forall n, 1 - sum_f_R0 salamin_sumand n <> 0).
  now intros m; apply Rgt_not_eq, denpos.
replace (salamin_formula (n + 1) - salamin_formula (n + 2)) with
  (4 * (u_ (n + 1) (/sqrt 2) ^ 2 - u_ (n + 2) (/sqrt 2)^ 2) /(1 - sum_f_R0 salamin_sumand n) +
   4 * u_ (n + 2) (/sqrt 2) ^ 2 * (/(1 - sum_f_R0 salamin_sumand n) -
   /(1 - sum_f_R0 salamin_sumand (n + 1)))); cycle 1.
  now unfold salamin_formula; rewrite -> n2m, n1m; field; auto.
assert (n211 : (n + 2 = (n + 1) + 1)%nat) by ring.
assert (u_v_bounds := u_v_s2_bound (n + 1)); rewrite <- n211 in u_v_bounds.
assert (u_v_bounds' := u_v_s2_bound n).
assert (dp : u_ (n + 2) (/sqrt 2) < u_ (n + 1) (/sqrt 2)).
  now assert (tmp := u_decr (n + 1)); rewrite n211; lt0.
assert (diffpos : 0 < u_ (n + 1) (/sqrt 2) ^ 2 - u_ (n + 2) (/sqrt 2) ^ 2).
  now rewrite diff_square; apply Rmult_lt_0_compat;lt0.
apply Rle_trans with (1 := Rabs_triang _ _); apply Rplus_le_compat.
  assert (u_ (n + 1) (/sqrt 2) ^ 2 - u_ (n + 2) (/sqrt 2) ^ 2 <
            8 * Rpower 531 (-2 ^ n)).
  apply Rlt_le_trans with (2 := proj2 (majoration_y_n_vs2 n)).
    apply Rlt_trans with (v_ (n + 1) (/sqrt 2) * (y_ (n + 1) (/sqrt 2) - 1)).
      unfold y_, Rdiv; rewrite -> Rmult_minus_distr_l, Rmult_1_r, Rmult_comm.
      rewrite -> Rmult_assoc, Rinv_l, Rmult_1_r;[ | lt0].
      rewrite diff_square; apply Rlt_le_trans with
          (2 * (u_ (n + 1)(/sqrt 2) - u_ (n + 2)(/sqrt 2))).
        apply Rmult_lt_compat_r;[lt0 |].
        now assert (tmp1 := u_decr (n + 1)); rewrite n211; lt0.
      now replace (n + 2)%nat with (S (n + 1)) by ring; rewrite u_step; lt0.
    replace (y_ (n + 1) (/sqrt 2) - 1) with (1 * (y_ (n + 1) (/sqrt 2) - 1))
       at 2 by ring.
    apply Rmult_lt_compat_r;[ assert (tmp := y_gt_1 _ (n + 1) ints)| ]; lt0.
  rewrite Rabs_right; cycle 1.
    apply Rle_ge, Rmult_le_pos;[apply Rmult_le_pos;lt0 | ].
    now apply Rlt_le, Rinv_0_lt_compat.
  unfold Rdiv; rewrite !(Rmult_assoc 4); apply Rmult_le_compat_l;[lt0 | ].
  rewrite -> (Rmult_comm _ (/ _)), (Rmult_assoc 2).
  apply Rmult_le_compat; try lt0.
    now apply Rlt_le, Rinv_0_lt_compat; auto.
  (* TODO : investigate why interval does not work here. *)
  replace 2 with (/ / 2) by field.
  apply Rinv_le_contravar; try lt0.
  assert (tmp := salamin_sum_ub n); lt0.
rewrite -> Rabs_mult, (Rmult_assoc 3); apply Rmult_le_compat; try lt0.
  assert (tmp : 4 / 5 <= u_ (n + 2) (/sqrt 2) <= 6 / 7) by lt0.
  now interval.
replace (n + 1)%nat with (S n) by ring; rewrite tech5.
assert (help : forall a b, 1 - (a + b) = 1 - a - b) by now intros; ring.
rewrite help.
replace (/(1 - sum_f_R0 salamin_sumand n) - /(1 - sum_f_R0 salamin_sumand n -salamin_sumand (S n))) with
(-salamin_sumand (S n) /((1 - sum_f_R0 salamin_sumand n) * (1 - sum_f_R0 salamin_sumand n - salamin_sumand (S n)))); cycle 1.
  field;split;[ rewrite <- help; exact (denn0 (S n)) | auto].
unfold Rdiv; rewrite -> Rmult_comm, Rabs_mult.
rewrite -> (Rmult_assoc 2), (Rmult_assoc (2 ^ _)), (Rmult_assoc (1 ^ _)).
apply Rmult_le_compat; try lt0.
  rewrite Rabs_right; cycle 1.
    apply Rle_ge, Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; auto.
    now rewrite <- help; apply (denpos (S n)).
  replace 2 with (/ / 2) by field; apply Rinv_le_contravar; try lt0.
  rewrite <- help, <- tech5.
  assert (tmp := conj (salamin_sum_ub n) (salamin_sum_ub (S n))).
  assert (asp : forall k,  0 <= sum_f_R0 salamin_sumand k).
    intros; apply cond_pos_sum.
    intros m; unfold salamin_sumand; case (m =? 0); try lt0.
    now apply Rmult_le_pos;[lt0 | apply pow2_ge_0].
  assert (tmpn := conj (asp n) (asp (S n))).
  assert (0 <= sum_f_R0 salamin_sumand n <= /10 /\ 
          0 <= sum_f_R0 salamin_sumand (S n) <= /10) by lt0.
  (* TODO : investigate why interval does not work here. *)
  now apply Rle_trans with ((8 / 10) * (8 / 10));[ | apply Rmult_le_compat]; lt0.
unfold salamin_sumand; simpl (S n =? 0); lazy iota.
replace (S n  - 1)%nat with n by lia.
rewrite -> Rabs_Ropp, Rabs_right; cycle 1.
  now apply Rle_ge, Rmult_le_pos;[ |assert (t := v_lt_u _ n ints)];lt0. 
apply Rmult_le_compat_l;[lt0 | ].
replace (u_ n (/sqrt 2) - v_ n (/sqrt 2)) with
  (v_ n (/sqrt 2) * (y_ n (/sqrt 2) - 1)); cycle 1.
  now unfold y_; field; destruct (v_lt_u _ n ints); lt0.
rewrite Rpow_mult_distr; apply Rmult_le_compat; try apply pow2_ge_0.
  now apply pow_incr; assert (t := conj (v_lt_u _ n ints) (u_decr n)); lt0.
assert (nm1 : n = ((n - 1) + 1)%nat) by lia.
replace (64 * Rpower 531 (-2 ^ n)) with
  ((8 * Rpower 531 (-2 ^ (n - 1))) ^ 2); cycle 1.
  field_simplify; simpl; rewrite -> !Rdiv_1, Rmult_1_r, <- Rpower_plus.
  rewrite <- Ropp_plus_distr.
  assert (help2 : forall a, a + a = 2 * a) by now intros; ring.
  rewrite -> (help2 (2 ^ _)), tech_pow_Rmult.
  now replace (S (n - 1)) with n by lia.
apply pow_incr; rewrite -> nm1 at 1 2.
apply majoration_y_n_vs2.
Qed.