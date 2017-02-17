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
exists (fun p => atan(snd p/m) - atan (fst p/m)); split.
  exists (Rgt 0) (Rlt 0); try (exists 0; intros; fourier).
  intros u v _ _; simpl; apply (is_RInt_derive (fun x => atan (x/m))).
    now intros x _; apply is_derive_atan_scal.
  intros x _; apply (@ex_derive_continuous R_AbsRing R_NormedModule).
  auto_derive; apply Rgt_not_eq, Rplus_le_lt_0_compat;[ | fourier].
  now apply (pow2_ge_0 (x * / m)).
replace PI with (PI/2 + PI/2) by field.
apply (filterlim_comp_2 (G := locally (PI/2)) (H := locally (PI/2))
           (fun x => atan (snd x/m)) (fun x =>  - (atan (fst x/m))) Rplus).
    apply (filterlim_comp _ _ _ snd (fun x => atan (x / m)) _
              (Rbar_locally p_infty));[apply filterlim_snd | ].
    apply (filterlim_comp _ _ _ (fun x => x / m) atan _ (Rbar_locally p_infty)).
      pattern p_infty at 2; replace p_infty with (Rbar_mult p_infty (/m)).
        apply (filterlim_Rbar_mult_r (/m)).
      now apply is_Rbar_mult_unique, is_Rbar_mult_p_infty_pos, Rinv_0_lt_compat.
    apply filter_le_trans with (1 := lim_atan_p_infty).
    now intros S; unfold at_left, within; apply filter_imp.
  apply (filterlim_comp _ _ _ fst (fun x => - atan (x / m)) _
             (Rbar_locally m_infty));[apply filterlim_fst | ].
  apply (filterlim_comp _ _ _ (fun x => atan (x / m)) Ropp _ (at_right(-PI/2))).
    apply
        (filterlim_comp _ _ _ (fun x => (x / m)) atan _ (Rbar_locally m_infty)).
      pattern m_infty at 2; replace m_infty with (Rbar_mult m_infty (/m)).
        now apply filterlim_Rbar_mult_r.
    now apply is_Rbar_mult_unique, is_Rbar_mult_m_infty_pos, Rinv_0_lt_compat.
  apply lim_atan_m_infty.
  replace (PI / 2) with (- (-PI / 2)) by field.
  apply filter_le_trans with (at_left (- (- PI / 2))).
    now apply filterlim_Ropp_right.
  now intros S; unfold at_left, within; apply filter_imp.
now apply (filterlim_plus (PI/2) (PI/2)).
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
