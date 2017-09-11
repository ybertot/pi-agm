(* This file was tested with coq 8.5.1 and coquelicot 2.1.1 *)

Require Import Reals Coquelicot.Coquelicot Fourier Psatz.

Lemma lim_atan_p_infty :
  filterlim atan (Rbar_locally p_infty) (at_left (PI/2)).
Proof.
assert (0 < PI) by (assert (t := PI2_RGT_0); psatzl R).
intros S [ep Pep].
set (e' := Rmin (PI/2) ep).
assert (0 < e') by now apply Rmin_glb_lt; destruct ep; auto; psatzl R.
assert (e' <= PI/2) by apply Rmin_l.
exists (tan (PI/2 - e')); intros x Px.
assert (atan x < PI/2) by (destruct (atan_bound x); psatzl R).
apply Pep;[|psatzl R].
change (Rabs (atan x - PI/2) < ep).
rewrite Rabs_left, Ropp_minus_distr;[| psatzl R].
apply Rlt_le_trans with (PI / 2 - atan (tan (PI / 2 - e'))).
  now apply Rplus_lt_compat_l, Ropp_lt_contravar, atan_increasing.
replace (atan (tan (PI / 2 - e'))) with (PI / 2 - e').
  now ring_simplify; apply Rmin_r.
apply tan_is_inj;[psatzl R | apply atan_bound | now rewrite atan_right_inv].
Qed.

Lemma lim_atan_m_infty :
  filterlim atan (Rbar_locally m_infty) (at_right (-PI/2)).
Proof.
apply filterlim_ext with (fun x => - (atan (- x))).
  now intros; rewrite atan_opp, Ropp_involutive.
apply (filterlim_comp _ _ _ (fun x => atan (- x)) Ropp _ (at_left (PI/2))).
  apply (filterlim_comp _ _ _ Ropp atan _ (Rbar_locally p_infty)).
    now apply filterlim_Rbar_opp.
  now apply lim_atan_p_infty.
replace (- PI / 2) with (- (PI / 2)) by field.
apply filterlim_Ropp_left.
Qed.

Lemma atan_left_inv x : - PI/ 2 < x < PI/ 2 -> atan(tan x) = x.
Proof.
intros intx.
destruct (atan_bound (tan x)).
destruct (Rtotal_order (atan(tan x)) x) as [abs | [it | abs]]; auto;
  now apply tan_increasing in abs; try psatzl R; rewrite atan_right_inv in abs;
          psatzl R.
Qed.

Lemma integral_atan_comp_scal m : 0 < m ->
   is_RInt_gen (fun x => /m * /((x / m) ^ 2 + 1)) 
       (Rbar_locally m_infty) (Rbar_locally p_infty) PI.
intros m0.
assert (is_derive_atan_scal : forall x,  
           is_derive (fun x => atan (x / m)) x (/ m * /((x/m)^2 + 1))).
  intros x; auto_derive; auto; field.
  split; apply Rgt_not_eq; auto; apply Rplus_le_lt_0_compat.
    now apply pow2_ge_0.
  now apply pow2_gt_0, Rgt_not_eq.
(* start experimenting here. *)
intros P [eps Peps].
set (eps' := Rmin eps (PI/ 2)).
exists (fun u => u < m * tan (-PI / 2 + eps' / 2))
    (fun u => m * tan (PI / 2 - eps' / 2) < u).
    apply (open_Rbar_lt' _ (m * tan (- PI / 2 + eps' / 2))); exact I.
  apply (open_Rbar_gt' _ (m * tan (PI / 2 - eps' / 2))); exact I.
intros x y cx cy; exists (atan (y/m) - atan (x/m)); split.
  simpl; apply (is_RInt_derive (fun x => atan (x/m))).
    now intros; apply is_derive_atan_scal.
  intros x' _; apply (@ex_derive_continuous R_AbsRing R_NormedModule).
  auto_derive; apply Rgt_not_eq, Rplus_le_lt_0_compat;[ | fourier].
  now apply (pow2_ge_0 (x' * / m)).
apply Peps.
change ((Rabs (atan (y / m) - atan (x / m) - PI)) < eps).
assert (ep2 : pos eps = pos_div_2 eps + pos_div_2 eps) by (simpl; field).
rewrite ep2.
replace (atan (y / m) - atan (x / m) - PI) with
        ((atan (y / m) - PI / 2) - (atan (x / m) - - PI / 2)) by field.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
assert (PIPOS := PI2_RGT_0).
assert (0 < eps').
  now apply Rmin_glb_lt;[apply cond_pos | ].
assert (eps' <= PI/2) by apply Rmin_r.
apply Rplus_lt_compat.
  rewrite Rabs_left; cycle 1.
    now destruct (atan_bound (y/m)); psatzl R.
  simpl; enough (PI/2 - eps/2 < atan(y/m)) by psatzl R.
  apply Rle_lt_trans with (PI / 2 - eps' / 2).
    apply Rplus_le_compat_l, Ropp_le_contravar, Rmult_le_compat_r;[psatzl R|].
    now unfold eps'; apply Rmin_l.
  rewrite <- (atan_left_inv (PI / 2 - eps' / 2));[ | psatzl R].
  apply atan_increasing.
  apply Rmult_lt_reg_r with m;[auto | ].
  now unfold Rdiv at 3; rewrite Rmult_assoc, Rinv_l; psatzl R.
destruct (atan_bound (x / m)).
rewrite Rabs_left;[ | psatzl R].
rewrite Ropp_involutive; simpl; apply Rlt_le_trans with (eps' / 2); cycle 1.
  now apply Rmult_le_compat_r;[psatzl R | apply Rmin_l].
enough (atan (x / m) < -PI/2 + eps' / 2) by psatzl R.
rewrite <- (atan_left_inv (_ + _));[ | psatzl R].
apply atan_increasing.
apply Rmult_lt_reg_r with m;[auto | ].
now unfold Rdiv at 1; rewrite Rmult_assoc, Rinv_l; psatzl R.
Qed.  

Lemma atan_derivative_improper_integral :
  is_RInt_gen (fun x => /(x ^ 2 + 1))
     (Rbar_locally m_infty) (Rbar_locally p_infty) PI.
Proof.
apply is_RInt_gen_ext with (fun x =>  /1 * /((x/1)^2 + 1)).
  exists (Rgt 0) (Rlt 0); try (exists 0; intros; psatzl R).
  intros x y _ _ z _; rewrite Rdiv_1, Rinv_1, Rmult_1_l; reflexivity.
apply integral_atan_comp_scal; psatzl R.
Qed.
