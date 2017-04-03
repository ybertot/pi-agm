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
auto_derive.
destruct (ex_derive_ag n x (proj1 intx)) as [d1 [d2 [du [dv _]]]].
repeat (split;[eapply ex_intro; eassumption| ]); psatzl R.
Qed.

(* This equation 42 in submitted version of "distant decimals of pi" *)
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
assert (help : forall x y, x ^ 2 - y ^ 2 = (x + y) * (x - y)) by (intros; ring).
assert (0 < v_ n x /\ 0 < u_ n x).
  now destruct (ag_le n 1 x); unfold v_, u_; psatzl R.
assert (v_ n x < u_ n x) by now apply v_lt_u.
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
destruct i as [|i];[rewrite Rmult_0_l; easy | simpl].
rewrite -> Nat.sub_0_r, u_step, v_step, !Rmult_1_r, sqrt_sqrt.
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
         Derive (v_ (n + 1)) s2)); cycle 1.
  now unfold s2 in *; field; lt0.
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
replace 54 with (6 * 9) by ring; rewrite (Rmult_assoc 6).
rewrite -> (Rmult_comm (_ - _)), Rabs_mult.
apply Rmult_le_compat; try lt0.
  rewrite Rabs_mult; replace 6 with (3 * (1 ^2 * 1 * 2)) by ring.
  apply Rmult_le_compat; try lt0.
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
  replace (exp (2 ^ (n - 1) * ln (/ 531))) with (Rpower (/531) (2 ^ (n - 1)));
    cycle 1.
    reflexivity.
  rewrite Rpower_mult_distr; try (unfold Rpower; lt0).
  rewrite <- (Rpower_1 531) at 1;try lt0;  rewrite <- Rpower_Ropp; try lt0.
  rewrite <- Rpower_plus; replace (-1 + 2) with 1 by ring.
  rewrite Rpower_1; try lt0.
  apply Rle_trans with (Rpower 531 1).
    unfold Rpower; interval.
  apply Rle_Rpower; try lt0.
  apply pow_R1_Rle; lt0.
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

Lemma salamin_sum_ub  n : sum_f_R0 salamin_sumand n < 4/10.
Proof.
apply Rmult_lt_reg_l with (1 - /4);[psatzl R | ].
apply Rle_lt_trans with  (/4 - ((/4) ^ (n + 1)));
   [ | enough (0 < (/4) ^ (n + 1)) by psatzl R; lt0].
induction n as [|n IHn].
  simpl; unfold salamin_sumand; simpl (0 =? 0)%nat; lazy iota.
  apply Req_le; field.
rewrite -> tech5, Rmult_plus_distr_l.
apply Rle_trans with (/4 - ((/4) ^ (n + 1)) + ((1 - /4) * ((/4) ^ (n + 1))));
  cycle 1.
  replace ((/4) ^ (S n + 1)) with ((/4) ^ (n + 1) * /4) by (simpl; ring).
  now apply Req_le; field.
apply Rplus_le_compat;[exact IHn | apply Rmult_le_compat_l;[lt0 | ]].
unfold salamin_sumand; simpl (S n =? 0); lazy iota.
replace (S n - 1)%nat with n by lia.
assert (zz : u_ n (/sqrt 2) - v_ n (/sqrt 2) < /2 * (/2) ^ n * (/2) ^ n).
  replace (u_ n (/sqrt 2) - v_ n (/sqrt 2)) with
     (v_ n (/sqrt 2) * (y_ n (/sqrt 2) - 1)); cycle 1.
    now unfold y_; field; destruct (v_lt_u _ n (ints)); lt0.
  apply Rlt_trans with (1 * (y_ n (/sqrt 2) - 1)).
    apply Rmult_lt_compat_r;[assert (t := y_gt_1 _ n ints); lt0 | ].
  now destruct (v_lt_u _ n ints); destruct ints;
    destruct (ag_le n 1 (/sqrt 2)); unfold u_, v_ in * |- *; lt0.
  rewrite Rmult_1_l.
    destruct n as [|n].
    unfold y_, u_, v_; simpl; interval.
  replace (S n) with (n + 1)%nat by lia.
  apply Rle_lt_trans with (1 := proj2 (majoration_y_n_vs2 n)).
  rewrite !pow_add; simpl; rewrite !Rmult_1_r.
  rewrite <- (exp_ln 8) at 1;[ | lt0]; unfold Rpower; rewrite <- exp_plus.
  rewrite <- (Rpower_pow _ (/2)); try lt0.
  rewrite <- (Rpower_1 (/2)) at 1 3 5; try lt0.
  unfold Rpower; rewrite -> Rmult_1_l, <- !exp_plus; apply exp_increasing.
  rewrite <- (Rplus_comm (ln (/2))), <- !Rplus_assoc, <- ln_mult; try lt0.
  rewrite <- (Rplus_comm (ln (/2))), <- Rplus_assoc, <- ln_mult; try lt0.
  rewrite -> Rplus_assoc, <- Rmult_plus_distr_l, <- ln_mult; try lt0.
  replace (/2 * (/2 * /2)) with (/8) by field.
  rewrite ln_Rinv; try lt0.
  apply Rplus_lt_reg_l with (ln 8); rewrite <- !Rplus_assoc, Rplus_opp_r.
  rewrite -> Rplus_0_l, <- ln_mult; try lt0.
  replace (ln 531) with (ln (531/4) + ln 4); cycle 1.
    now rewrite <- ln_mult; try lt0; replace (531/4 * 4) with 531 by field.
  rewrite -> (Rmult_plus_distr_l (-2 ^ n)), <- Rplus_assoc.
  rewrite <- (Rplus_0_l (INR n * ln (/2 * /2))).
  apply Rplus_lt_compat.
  enough (ln (8 * 8) < 2 ^ n * ln (531/4)) by psatzl R.
    apply Rmult_lt_reg_r with (/ln (531 / 4));[interval | ].
    rewrite -> !(Rmult_assoc _ _ (/ln (531/4))), Rinv_r, Rmult_1_r;
     [ | interval].
    apply Rlt_le_trans with 1;[interval | apply pow_R1_Rle; lt0].
  replace (/2 * /2) with (/ 4) by field.
  rewrite -> ln_Rinv, <-Ropp_mult_distr_r, <- Ropp_mult_distr_l; try lt0.
  apply Ropp_lt_contravar; apply Rmult_lt_compat_r;[interval | ].
  clear.
  induction n;[simpl; lt0 |
     rewrite S_INR; replace (2 ^ S n) with (2 ^ n + 2 ^ n) by (simpl; ring)].
  apply Rplus_lt_le_compat; auto; apply pow_R1_Rle; lt0.
assert (z1 : 0 <= u_ n (/sqrt 2) - v_ n (/sqrt 2))
   by (assert (t := v_lt_u _ n ints); psatzl R).
apply Rle_trans with (2 ^ n * (/2 * (/2) ^ n * (/2) ^ n) ^ 2).
  apply Rmult_le_compat_l;[lt0 | apply pow_incr; lt0].
simpl; rewrite -> Rmult_1_r, -> pow_add, pow_1, <- (Rmult_comm (/4)).
rewrite -> !Rmult_assoc, <- Rpow_mult_distr, <- (Rmult_assoc (/2)).
rewrite -> (Rmult_comm (/2)), <- !Rmult_assoc, <- Rpow_mult_distr.
rewrite -> Rinv_r, pow1, Rmult_1_l; try lt0.
rewrite <- (Rmult_comm (/2)), <- (Rmult_assoc (/2)).
replace (/2 * / 2) with (/4) by field.
apply Rmult_le_compat_r;[lt0 | enough ((/2) ^ n <= 1) by psatzl R].
clear; induction n as [ | n IHn].
   apply Req_le; reflexivity.
now simpl; psatzl R.
Qed.

(* TODO : report bug, auto_derive stops functioning if this import
  appears too early. *)
Require Import rounding_correct.

(*TODO rempove this line once rounding_correct is recompiled. *)

Open Scope R_scope.
Section rounded_operations.

Variables (e : R) (r_div : R -> R -> R) (r_sqrt : R -> R)
           (r_mult : R -> R -> R)(r_square : R -> R).

Hypothesis ce : 0 < e < /1000.

Hypothesis r_mult_spec :
  forall x y, 0 <= x -> 0 <= y -> x * y - e < r_mult x y <= x * y.

Hypothesis r_div_spec :
  forall x y, (0 < y) -> x/y - e < r_div x y <= x/y.

Hypothesis r_sqrt_spec :
  forall x, 0 <= x -> sqrt x - e < r_sqrt x <= sqrt x.

Hypothesis r_square_spec :
  forall x, x ^ 2 - e < r_square x <= x ^ 2.

Lemma sumand_error_ub  u v e' h h' k :
0 <= e' <= / 1000 ->
e <= e' ->
-e' <= h <= 0 -> -e' <= h' <= 0 ->
2 * e' <= / 4 * / 2 ^ k ->
0 <= u - v <= /4 * / 2 ^ k ->
2 ^ k * r_square ((u + h) - (v + h')) <= 2 ^ k * (u - v) ^ 2 + 2 / 3 * e'.
Proof.
intros (* intu intv *) inte' ee' inth inth' ek uv.
assert (-/1000 <= h <= 0) by psatzl R.
assert (-/1000 <= h' <= 0) by psatzl R.
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help3 : forall a b, a < b -> 0 < b -> a / b <= 1).
   intros a b ab b0; apply Rmult_le_reg_r with b;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c, a = (b - c) / e' -> b = c + a * e').
  now intros a b c q; rewrite -> q; field; psatzl R.
assert (exists e1, r_square ((u + h) - (v + h')) =
                       ((u + h) - (v + h')) ^ 2 + e1 * e' /\
                   - 1  <= e1 <= 0) as [e1 [Q Pe1]];[| rewrite Q; clear Q].
  destruct (r_square_spec((u + h) - (v + h'))); try psatzl R.
    eapply ex_intro;split;[eapply help4, refl_equal | ].
  now split;[apply help1 | apply help2]; psatzl R.
rewrite Rmult_plus_distr_l.
replace ((u + h - (v + h')) ^ 2) with
         ((u - v) ^ 2 + 2 * (u - v) * (h - h') + (h - h') ^ 2)
  by ring.
rewrite -> !(Rplus_assoc ((u - v) ^ 2)), Rmult_plus_distr_l, Rplus_assoc.
apply Rplus_le_compat_l; rewrite <- Rmult_plus_distr_l.
(* TODO : understand why this does not work. 
replace ((3 / 4 + 2 ^ k)  * e') with ((/2 * e' + /4 * e') + 2 ^ k * e') at 2 by field. *)
apply Rle_trans with (/2 * e' + / 6 * e' + 0);[|apply Req_le; field].
rewrite !(Rmult_plus_distr_l (2 ^ k)); apply Rplus_le_compat.
  apply Rplus_le_compat;[rewrite <- Rmult_assoc | ]. 
    destruct (Rle_dec 0 (h - h')).
      apply Rmult_le_compat; try lt0.
        now repeat apply Rmult_le_pos; lt0.
      rewrite <- Rmult_assoc; apply Rmult_le_reg_l with (/(2 ^ k * 2)); try lt0.
      rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
      now apply Rle_trans with (1 := proj2 uv), Req_le; field; lt0.
    apply Rle_trans with (2 ^ k * (2 * (u - v)) * 0).
      apply Rmult_le_compat_l.
        repeat apply Rmult_le_pos; lt0.
      lt0.
    now rewrite Rmult_0_r; lt0.
  destruct (Rle_dec 0 (h - h')).
    replace (2 ^ k * (h - h') ^ 2) with (2 ^ k * (h - h') * (h - h')) by ring.
    apply Rmult_le_compat; try lt0.
      apply Rmult_le_pos; lt0.
    apply Rmult_le_reg_l with (/ 2 ^ k);[lt0 |].
    now rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; lt0.
    replace (2 ^ k * (h - h') ^ 2) with (2 ^ k * (h' - h) * (h' - h)) by ring.
  apply Rmult_le_compat; try lt0.
  apply Rmult_le_reg_l with (/ 2 ^ k);[lt0 |].
  now rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; lt0.
enough (0 <= - (2 ^ k * (e1 * e'))) by psatzl R.
rewrite -> Ropp_mult_distr_r, Ropp_mult_distr_l.
now repeat apply Rmult_le_pos; lt0.
Qed.

Lemma sumand_error_lb  u v e' h h' k :
(*
42/50 <= u <= 43/50 -> 42/50 <= v <= 43/50 -> *)
0 <= e' <= / 1000 ->
e <= e' ->
-e' <= h <= 0 -> -e' <= h' <= 0 ->
2 * e' <= /4 * / 2 ^ k ->
0 <= u - v <= /4 * / 2 ^ k ->
2 ^ k * (u - v) ^ 2 - (2 / 3  + 2 ^ k) * e' <=
   2 ^ k * r_square ((u + h) - (v + h')).
Proof.
intros inte' ee' inth inth' ek uv.
assert (-/1000 <= h <= 0) by psatzl R.
assert (-/1000 <= h' <= 0) by psatzl R.
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help3 : forall a b, a < b -> 0 < b -> a / b <= 1).
   intros a b ab b0; apply Rmult_le_reg_r with b;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c, a = (b - c) / e' -> b = c + a * e').
  now intros a b c q; rewrite -> q; field; psatzl R.
assert (exists e1, r_square ((u + h) - (v + h')) =
                       ((u + h) - (v + h')) ^ 2 + e1 * e' /\
                   - 1 <= e1 <= 0) as [e1 [Q Pe1]];[| rewrite Q; clear Q].
  destruct (r_square_spec((u + h) - (v + h'))); try psatzl R.
    eapply ex_intro;split;[eapply help4, refl_equal | ].
  now split;[apply help1 | apply help2]; psatzl R.
rewrite (Rmult_plus_distr_l (2 ^ k)).
replace ((u + h - (v + h')) ^ 2) with
         ((u - v) ^ 2 + 2 * (u - v) * (h - h') + (h - h') ^ 2)
  by ring.
rewrite -> !(Rplus_assoc ((u - v) ^ 2)), (Rmult_plus_distr_l (2 ^ k)), Rplus_assoc.
apply Rplus_le_compat_l; rewrite <- Rmult_plus_distr_l.
apply Rle_trans with ((-/2 * e' + -/ 6 * e') + (2 ^ k) * (- 1 * e'));
  [apply Req_le; field|].
rewrite !(Rmult_plus_distr_l (2 ^ k)); apply Rplus_le_compat.
  apply Rplus_le_compat;[rewrite <- Rmult_assoc | ]. 
    destruct (Rle_dec 0 (h - h')).
      apply Rle_trans with 0; try lt0.
      now repeat apply Rmult_le_pos; lt0.
    enough (2 ^ k * (2 * (u - v)) * (h' - h) <= /2 * e') by psatzl R.
    apply Rmult_le_compat; try lt0.
      now apply Rmult_le_pos; lt0.
    rewrite <- Rmult_assoc; apply Rmult_le_reg_l with (/(2 ^ k * 2)); try lt0.
    rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
    now apply Rle_trans with (1 := proj2 uv), Req_le; field; lt0.
  now apply Rle_trans with 0;[| apply Rmult_le_pos;[| apply pow2_ge_0 ]];lt0.
apply Rmult_le_compat_l;[lt0 | apply Rmult_le_compat_r; lt0].
Qed.

Lemma agm1_error e' a b h h':
-e' <= h <= 0 -> -e' <= h' <= 0 ->
  (a + b) / 2 - e' <= ((a + h) + (b + h')) / 2 <= (a + b)/2.
Proof.
split;[ | psatzl R].
replace ((a + h + (b + h')) / 2) with ((a + b) / 2 + (h + h') / 2) by field.
now apply Rplus_le_compat_l; psatzl R.
Qed.

Lemma agm2_error e' u v h h' :
  85355/100000 <= u <= 85356/100000 ->
  84089/100000 <= v <= 84090/100000 ->
  0 <= e' <= /100000 ->
  e <= / 10 * e' ->
  e' <= h <= 0 -> e' <= h' <= 0 ->
  sqrt (u * v) - 3/ 2 * e' <= r_sqrt (r_mult (u + h) (v + h')) <= sqrt (u * v).
Proof.
intros intu intv inte' ee' inth inth'.
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help3 : forall a b, a < b -> 0 < b -> a / b <= 1).
   intros a b ab b0; apply Rmult_le_reg_r with b;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c, a = (b - c) / e' -> b = c + a * e').
  now intros a b c q; rewrite -> q; field; psatzl R.
assert (exists e1, r_mult (u + h) (v + h') =
                       (u + h) * (v + h') + e1 * e' /\
                   - /10 <= e1 <= 0) as [e1 [Q Pe1]];[| rewrite Q; clear Q].
  now destruct (r_mult_spec (u + h) (v + h')); try psatzl R.
assert (exists e2, r_sqrt ((u + h) * (v + h') + e1 * e') =
                       sqrt ((u + h) * (v + h') + e1 * e') + e2 * e' /\
                   - /10 <= e2 <= 0) as [e2 [Q Pe2]];[| rewrite Q; clear Q].
  destruct (r_sqrt_spec((u + h) - (v + h'))); try psatzl R.
split; cycle 1.
  apply Rle_trans with ((sqrt (u * v + 0)) + e2 * e').
    assert (-/100000 <= h <= 0) by psatzl R.
    assert (-/100000 <= h' <= 0) by psatzl R.
    apply Rplus_le_compat_r, sqrt_le_1;[interval | interval | ].
    replace ((u + h) * (v + h')) with 
        ((u * v) + (u + h) * h' + v * h) by ring.
    now rewrite !Rplus_assoc; apply Rplus_le_compat_l; interval.
  rewrite <- (Rplus_0_r (sqrt (u * v))); apply Rplus_le_compat.
    now rewrite Rplus_0_r; apply Req_le.
  now assert (pn : 0 <= -(e2 * e')) by lt0; psatzl R.
replace (sqrt (u * v) - 3/2 * e') with
   (sqrt (u * v) - 7/5 * e' - /10 * e') by field.
apply Rplus_le_compat;[|rewrite Ropp_mult_distr_l; apply Rmult_le_compat_r;lt0].
assert (sf : ((u + h) * (v + h') + e1 * e' =
          u * v + h' * (u + h) + h * v + e1 * e')) by ring.
assert (cmp : (u + h) * (v + h') + e1 * e' <= u * v).
  replace (u * v) with (u * v + 0) by ring.
  rewrite -> sf, !Rplus_assoc; apply Rplus_le_compat_l.
  assert (0 < u + h) by psatzl R.
  assert (help : forall a, 0 <= -a -> a <= 0) by (intros; psatzl R); apply help.
  now rewrite -> !Ropp_plus_distr, !Ropp_mult_distr_l; lt0.
assert (mnh : Rmin (u * v) ((u + h) * (v + h') + e1 * e') =
                    ((u + h) * (v + h') + e1 * e')).
   now rewrite Rmin_right; lt0.
assert (mxh : Rmax (u * v) ((u + h) * (v + h') + e1 * e') = u * v).
   now rewrite Rmax_left; lt0.
assert ( -/100000 <= h <= 0) by psatzl R.
assert ( -/100000 <= h' <= 0) by psatzl R.
assert ( 0 <= e' <= /100000) by psatzl R.
set (a0 := Rmin (u * v) ((u + h) * (v + h') + e1 * e')).
set (b0 := Rmax (u * v) ((u + h) * (v + h') + e1 * e')).
assert (0 < a0) by (unfold a0; rewrite mnh; interval).
assert (ds' : forall x, a0 <= x <= b0 -> 
           is_derive sqrt x ((fun y => 1 / (2 * sqrt x)) x)).
  intros x intx; auto_derive;[| field]; psatzl R.
assert (ds : forall x, a0 < x < b0 -> 
           is_derive sqrt x ((fun y => 1 / (2 * sqrt x)) x)).
  now intros; apply ds'; psatzl R.
assert (sc : forall x : R, a0 <= x <= b0 -> continuity_pt sqrt x).
  intros x intx; apply sqrt_continuity_pt; psatzl R.
destruct (MVT_gen sqrt (u * v) ((u + h) * (v + h') + e1 * e')
              (fun y => 1 / (2 * sqrt y))
              ds sc) as [c PC].
rewrite -> mnh, mxh in PC.
assert (help : forall a b c, -(c - a) <= b -> a - b <= c) by (intros; psatzl R).
apply help; clear help; rewrite -> (proj2 PC), sf, !(Rplus_assoc (u * v)).
unfold Rminus; rewrite -> (Rplus_comm (u * v)), (Rplus_assoc _ (u * v)).
rewrite -> Rplus_opp_r, Rplus_0_r.
interval_intro ((u + h) * (v + h') + e1 * e') as uvh.
interval_intro (u * v) as uv.
assert (t := conj (Rle_trans _ _ _ (proj1 uvh) (proj1 (proj1 PC)))
                (Rle_trans _ _ _ (proj2 (proj1 PC)) (proj2 uv))).
interval_intro (1 / (2 * sqrt c)).
interval_intro (u + h) as uh; rewrite -> Ropp_mult_distr_r, !Ropp_plus_distr.
rewrite !Ropp_mult_distr_l.
apply Rle_trans with ((1 / (2 * sqrt c)) * (e' * (u + h) + e' * v + e' * - e1)).
  apply Rmult_le_compat_l;[lt0 | ].
  rewrite !Rplus_assoc; apply Rplus_le_compat;[apply Rmult_le_compat_r;lt0 | ].
  apply Rplus_le_compat;[apply Rmult_le_compat_r;lt0|].
  rewrite Rmult_comm; apply Rmult_le_compat_l; lt0.
  rewrite <- !Rmult_plus_distr_l, (Rmult_comm e'), <- Rmult_assoc.
  apply Rmult_le_compat_r;[lt0|].
interval.
Qed.

(* TODO : transfer back to elliptic integral.v *)
Lemma agm_conv_speed a b c n : 0 < a -> /4 <= b -> b <= a -> a - b <= c ->
  c < 1 -> fst (ag a b n) - snd (ag a b n) <= c ^ (2 ^ n).
Proof.
revert a b c; induction n as [|n IHn].
  simpl; intros a b a0 b1 ba bma c1; psatzl R.
simpl; intros a b c a0 b1 ab bma c1.
assert (b0 : 0 < b) by psatzl R.
change (2 ^ n + (2 ^ n + 0))%nat with (2 * (2 ^ n))%nat.
assert ((a + b) / 2 - sqrt (a * b) <= c ^ 2).
  assert (t := ag_le 1 a b a0 b0 ab); simpl in t; destruct t as [bsq [ga ara]].
  rewrite agm_diff; auto.
  apply Rle_trans with ((a - b) ^ 2 / 1).
    apply Rmult_le_compat_l;[apply pow2_ge_0 | ].
    now apply Rinv_le_contravar; psatzl R.
  simpl; unfold Rdiv; rewrite -> Rinv_1, !Rmult_1_r.
  now apply Rmult_le_compat; lt0.
rewrite pow_mult; apply IHn.
        now lt0.
      replace (/ 4) with (sqrt (/4 * /4)) by (rewrite sqrt_square; lt0).
      now apply sqrt_le_1_alt, Rmult_le_compat; psatzl R.
    now generalize (ag_le 1 a b a0 b0 ab); simpl; intros; psatzl R.
  now easy.
now destruct (pow_lt_1_compat c 2); try lia; psatzl R.
Qed.

Lemma sum_error s h h' k e' (k1 : (1 <= k)%nat) :
  0 <= e' <= /10 ^ (k + 3) / 2 ^ k ->
  e <= / 10 * e' ->
  -((3 / 2) ^ (k - 1) * e') <= h <= 0 ->
  -((3 / 2) ^ (k - 1) * e') <= h' <= 0 ->
  Rabs (s - (1 - sum_f_R0 salamin_sumand k)) <= 3 ^ k / 2 * e' ->
  Rabs ((s - 2 ^ k * r_square ((u_ k (/sqrt 2) + h) - (v_ k (/sqrt 2) + h')))
        - (1 - sum_f_R0 salamin_sumand (S k))) <= 3 ^ (S k) / 2 * e'.
Proof.
intros inte' ee' inth inth' cs.
assert (ls : 3 ^ S k / 2 * e' = 3 ^ k / 2 * e' + 3 ^ k * e').
  now rewrite <- Rmult_plus_distr_r, <- tech_pow_Rmult; field.
rewrite -> ls, tech5.
assert (help : forall a b c d, a - b - (1 - (c + d)) = a - (1 - c) + (d - b))
  by (intros; ring).
rewrite help; clear help; apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat; try lt0.
assert (0 <= (3 / 2) ^ (k - 1) * e' <= /1000).
  split;[lt0 | ].
  apply Rmult_le_reg_l with (/(3 / 2) ^ (k - 1));[lt0 | ].
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;
    [apply Rle_trans with (1 := proj2 inte')| lt0].
  unfold Rdiv; rewrite -> (Rmult_comm (/10 ^ (k + 3))).
  apply Rmult_le_compat; try lt0; cycle 1.
    apply Rle_Rinv; try lt0; replace 1000 with (10 ^ 3) by ring; apply Rle_pow.
      now lt0.
    now lia.
  apply Rle_Rinv;[lt0 | lt0 | apply Rle_trans with ((3/2) ^ k)].
    now apply Rle_pow;[lt0 | lia].
  now apply pow_incr; psatzl R.
assert (e <= (3 / 2) ^ (k - 1) * e').
  apply Rle_trans with (1 := ee'); apply Rmult_le_compat_r;[lt0 | ].
  now apply Rle_trans with 1;[| apply pow_R1_Rle]; psatzl R.
assert (0 <= u_ k (/sqrt 2) - v_ k (/sqrt 2) <= /4 * / 2 ^ k).
  split.
    now apply Rlt_le, Rlt_Rminus, v_lt_u, ints.
  assert (s24 : /4 <= /sqrt 2) by interval.
  assert (s21 : /sqrt 2 <= 1) by interval.
  assert (s2m : 1 - /sqrt 2 < 1) by interval.
  assert (t := agm_conv_speed 1 (/sqrt 2) (1 - /sqrt 2) k Rlt_0_1 s24 s21
               (Rle_refl _) s2m).
  apply Rle_trans with (1 := t); clear t.
  apply Rlt_le, ln_lt_inv;[apply pow_lt; interval | lt0 | ].
  rewrite <- Rpower_pow;[|interval].
  unfold Rpower; rewrite ln_exp.
  clear -k1; induction k1.
    now simpl; rewrite Rmult_1_r; interval.
  rewrite -> Nat.pow_succ_r, mult_INR, Rmult_assoc; simpl INR; auto with arith.
  apply Rlt_trans with (2 * ln (/4 * /2 ^ m)).
    apply Rmult_lt_compat_l;[lt0 | assumption ].
  rewrite <- tech_pow_Rmult, (Rinv_mult_distr 2 (2 ^ m));[ | lt0 | lt0].
  replace (2 * ln (/ 4 * / 2 ^ m)) with (ln (/4 * /2 ^ m) + ln (/4 * /2 ^ m))
     by ring.
  rewrite !ln_mult; try lt0; rewrite <- !Rplus_assoc; apply Rplus_lt_compat_r.
  rewrite Rplus_assoc; apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (ln (/2) + ln (/4));[ | interval].
  apply Rplus_le_compat_r; rewrite !ln_Rinv; try lt0.
  apply Ropp_le_contravar, ln_le; try lt0.
  now replace 2 with (2 ^ 1) at 1 by ring; apply Rle_pow; auto; lt0.
assert (2 * ((3 / 2) ^ (k - 1) * e') <= /4 * / 2 ^ k).
  apply Rle_trans with (2 * ((3 / 2) ^ k * (/10 ^ (k + 3) / 2 ^ k))).
    repeat (apply Rmult_le_compat; try lt0).
    now apply Rle_pow; try lia; psatzl R.
  replace (10 ^ (k + 3)) with (1000 * 10 ^ k) by
     (rewrite -> pow_add, Rmult_comm; ring).
  rewrite Rinv_mult_distr; try lt0; unfold Rdiv.
  rewrite !Rinv_pow; try lt0.
  rewrite -> (Rmult_assoc (/_)), <- Rpow_mult_distr, <- (Rmult_assoc _ (/_)).
  rewrite <- (Rmult_comm (/_)), (Rmult_assoc (/_)), <- Rpow_mult_distr.
  rewrite <- Rmult_assoc; apply Rmult_le_compat; try lt0.
  now apply pow_incr; psatzl R.
destruct (Rle_dec 0 (salamin_sumand (S k) -
                 2 ^ k * r_square (u_ k (/sqrt 2) + h - (v_ k (/sqrt 2) + h')))).
  rewrite Rabs_right; [|apply Rle_ge; assumption].
  assert (help : forall a b c, a - c <= b -> a - b <= c) by (intros; psatzl R).
  apply help; clear help.
  apply Rle_trans with (2 ^ k * (u_ k (/ sqrt 2) - v_ k (/ sqrt 2)) ^ 2 -
      (2 / 3 + 2 ^ k) * ((3 / 2) ^ (k - 1) * e')); cycle 1.
    assert (t := sumand_error_lb (u_ k (/sqrt 2)) (v_ k (/sqrt 2))
               ((3/2) ^ (k - 1) * e') h h' k ).
    now apply t; auto; clear t.
  apply Rplus_le_compat;[apply Req_le | ].
    unfold salamin_sumand; simpl (S k =? 0); lazy iota.
    now replace (S k - 1)%nat with k by lia.
  apply Ropp_le_contravar; rewrite <- Rmult_assoc; apply Rmult_le_compat_r;[lt0|].
  replace k with (S (k - 1)) at 1 by lia.
  rewrite <- tech_pow_Rmult, Rmult_plus_distr_r, Rmult_assoc, <- Rpow_mult_distr.
  replace (2 * (3 / 2)) with 3 by field.
  apply Rle_trans with (3 ^ (k - 1) + 2 * 3 ^ (k - 1)).
    apply Rplus_le_compat_r.
    destruct (k - 1)%nat as [ | n'];[simpl; psatzl R | ].
    rewrite <- !tech_pow_Rmult, <- Rmult_assoc; apply Rmult_le_compat; try lt0.
    now apply pow_incr; psatzl R.
  apply Req_le.
  replace (3 ^ (k - 1)) with (1 * 3 ^ (k - 1)) at 1 by ring.
  rewrite <- Rmult_plus_distr_r, tech_pow_Rmult; replace (S (k - 1)) with k by lia.
  replace (3 ^ (k + 1)) with (3 * 3 ^ k);[ field | ].
  now rewrite pow_add; simpl (3 ^ 1); ring.
rewrite Rabs_left;[ |lt0 ].
assert (help : forall a b c, b <= a + c -> -(a - b) <= c) by (intros; psatzl R).
apply help; clear help.
apply Rle_trans  with (2 ^ k * (u_ k (/ sqrt 2) - v_ k (/ sqrt 2)) ^ 2 +
      2 / 3 * ((3 / 2) ^ (k - 1) * e')); cycle 1.
  apply Rplus_le_compat.
    unfold salamin_sumand; simpl (S k =? 0); lazy iota.
    now replace (S k - 1)%nat with k by lia; apply Req_le.
  replace k with (S (k - 1)) at 2 by lia.
  rewrite <- tech_pow_Rmult, <- Rmult_assoc.
  apply Rmult_le_compat_r;[lt0 | apply Rmult_le_compat; try lt0].
  now apply pow_incr; psatzl R.
assert (t := sumand_error_ub (u_ k (/sqrt 2)) (v_ k (/sqrt 2)) ((3/2) ^ (k - 1) * e')
                 h h' k ).
now apply t; auto.
Qed.

Fixpoint rsalamin_rec (n : nat)
   (a b am1 bm1 sum twopk :R) :=
  match n with
    0 => r_div (4 * r_square a) sum
  | S p => (rsalamin_rec p (r_div (a + b) 2) (r_sqrt (r_mult a b)) a b
            (let v := (am1 - bm1) in
            sum - (twopk * r_square v)))%R (2 * twopk)
  end.

Definition rsalamin (n : nat) :=
  let s2 := r_div 1 (r_sqrt 2) in
  let a1 := r_div (1 + s2) 2 in
  let b1 := r_sqrt s2 in
  let twopk := 1 in
  rsalamin_rec n a1 b1 1 s2 1 twopk.

Lemma toto : True.
generalize (lim_salamin).
unfold salamin_formula.
unfold salamin_sumand.
Fixpoint fib n a b := match n with 0 => a | S p => fib p b (a + b)%Z end.
Compute fib 3 1 1.
Compute fib 10 1 1.
Compute fib 12 1 1.
Lemma rsalamin_rec_correct n p a b am1 bm1 sum twopk ha hb ha1 hb1 hsm :
  (1 <= n)%nat ->
  a = u_ n (/sqrt 2) + ha -> b = v_ n (/sqrt 2) + hb ->
  am1 = u_ (n - 1) (/sqrt 2) + ha1 -> bm1 = v_ (n - 1) (/sqrt 2) + hb1 ->
  sum = 1 - sum_f_R0 salamin_sumand (n - 1) + hsm ->
  twopk = 2 ^ (n - 1) ->
  - (3 / 2) ^ n * e <= ha <= 0 ->
  - (3 / 2) ^ n * e <= hb <= 0 ->
  - (3 / 2) ^ (n - 1) * e <= ha1 <= 0 ->
  - (3 / 2) ^ (n - 1) * e <= hb1 <= 0 ->
  Rabs hsm < 3 ^ n / 2 * e ->
  0 <= e <= / 10 ^ (n + p + 4) / 3 ^ (n + p) ->
  Rabs (rsalamin_rec p a b am1 bm1 sum twopk -
        ((4 * u_ n (/sqrt 2) ^ 2) /
        (1 - sum_f_R0 salamin_sumand ((p + n) - 1)))) < 3 ^ (p + n) * e + 10 * e.
Proof.
revert a b am1 bm1 sum twopk ha hb ha1 hb1 hsm.
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help3 : forall a b, a < b -> 0 < b -> a / b <= 1).
   intros a b ab b0; apply Rmult_le_reg_r with b;[psatzl R | ].
   now unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c e', 0 < e' -> a = (b - c) / e' -> b = c + a * e').
  now intros a b c e' e'pos q; rewrite -> q; field; psatzl R.
assert (help : forall a b c, a + b - c = a - c + b) by (intros; ring).
induction p.
  intros a b am1 bm1 sum twopk ha hb ha1 hb1 hsm n1 aq bq a1q b1q sq tq
   intha inthb inta1 intb1 intsm inte.
  assert (-/100 <= hsm <= /100).
    apply Fcore_Raux.Rabs_le_inv, Rlt_le, Rlt_trans with (1 := intsm).
    apply Rle_lt_trans with (3 ^ n/2 * (/10 ^ (n + 0 + 4) / 3 ^ (n + 0))).
    now apply Rmult_le_compat_l;lt0.
    replace 100 with (Rpower 10 2) by
          (replace 100 with (10 ^ 2) by ring; rewrite <- Rpower_pow; auto; lt0).
    assert (0 < Rpower 10 2) by (unfold Rpower; lt0).
    rewrite Nat.add_0_r; field_simplify; try split; try lt0.
    unfold Rdiv; rewrite !Rmult_1_l; rewrite  <- (Rpower_1 2) at 1; try lt0.
    rewrite <- Rpower_pow; try lt0; unfold Rpower.
    rewrite <- exp_plus, <- !exp_Ropp; apply exp_increasing.
    assert (0 < ln 2) by interval; assert (0 < ln 10) by interval.
    rewrite plus_INR; replace (INR 4) with 4 by (simpl; ring).
    rewrite Rmult_plus_distr_r; enough (0 <= n * ln 10) by lt0.
    now apply Rmult_le_pos; try lt0; apply pos_INR.
  unfold rsalamin_rec.
  rewrite -> aq, sq.
  assert (exists e1, r_square (u_ n (/ sqrt 2) + ha) =
                       (u_ n (/sqrt 2) + ha) ^ 2 + e1 * e  /\
                   - 1 <= e1 <= 0) as [e1 [Q Pe1]];[| rewrite Q; clear Q].
    destruct (r_square_spec (u_ n (/ sqrt 2) + ha)); try psatzl R.
    eapply ex_intro;split;[apply  help4;[psatzl R | reflexivity ] | ].
    now split;[apply help1| apply help2]; psatzl R.
  assert (exists e2, r_div (4 * ((u_ n (/ sqrt 2) + ha) ^ 2 + e1 * e))
       (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) =
       (4 * ((u_ n (/ sqrt 2) + ha) ^ 2 + e1 * e)) /
       (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) + e2 * e /\
       -1 <= e2 <= 0) as [e2 [Q Pe2]];[| rewrite Q; clear Q].
     destruct (r_div_spec (4 * ((u_ n (/ sqrt 2) + ha) ^ 2 + e1 * e))
       (1 - sum_f_R0 salamin_sumand (n - 1) + hsm)); try psatzl R.
      assert (t := salamin_sum_ub (n - 1)); psatzl R.
    eapply ex_intro;split;[apply  help4;[psatzl R | reflexivity ] | ].
    now split;[apply help1| apply help2]; psatzl R.
  rewrite help; apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (3 ^ (0 + n) * e + 10 * e) with (3 ^ n * e + 1 * e + 8 * e + 1 * e) by
    (rewrite Nat.add_0_l; ring).
  apply Rplus_lt_le_compat; cycle 1.
    rewrite -> Rabs_mult, (Rabs_right e);[ | lt0]; apply Rmult_le_compat_r.
      now lt0.
    now rewrite Rabs_left1; psatzl R.
  rewrite -> Rmult_plus_distr_l, Rdiv_plus_distr, help.
  assert (ssub := salamin_sum_ub (n - 1)).
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat; cycle 1.
    assert (/ (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) < 2).
      rewrite <- (Rinv_involutive 2); try lt0; apply Rinv_lt_contravar.
        apply Rmult_lt_0_compat; try lt0.
      now assert (t := salamin_sum_ub (n -1)); lt0.
    replace (8 * e) with (4 * e * 2) by ring.
    rewrite Rabs_left1; cycle 1.
      apply Rmult_le_0_r;[apply Rmult_le_0_l | ]; try lt0.
      now apply Rmult_le_0_r; lt0.
    apply Rle_lt_trans with
        (4 * e * / (1 - sum_f_R0 salamin_sumand (n - 1) + hsm)).
      unfold Rdiv; rewrite !(Ropp_mult_distr_l (4 * (e1 * e))).
      apply Rmult_le_compat_r;[lt0 | ].
        rewrite -> Ropp_mult_distr_r, Ropp_mult_distr_l.
      apply Rmult_le_compat_l;[lt0 | ].
      now rewrite <- (Rmult_1_l e) at 2; apply Rmult_le_compat_r; lt0.
    now apply Rmult_lt_compat_l; lt0.

      Search