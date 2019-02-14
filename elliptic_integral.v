Require Import Reals Coquelicot.Coquelicot Psatz.
Require Import filter_Rlt atan_derivative_improper_integral.
Require Import generalities.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

Definition ellf (a b x : R) := /sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)).

Lemma elliptic_integrable a b : 0 < a -> 0 < b ->
ex_RInt_gen
 (fun x => /sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))
 (Rbar_locally m_infty) (Rbar_locally p_infty).
Proof.
intros a0 b0; set (m := Rmin a b).
assert (0 < m) by now apply Rmin_glb_lt; auto.
assert (m <= a) by apply Rmin_l.
assert (m <= b) by apply Rmin_r.
set (g := (fun x => /m * (/m * /((x /m) ^ 2 + 1))));
apply (ex_RInt_gen_bound g); try solve[apply Rbar_locally_filter ].
    apply filter_Rlt_witness with 0; exists 0; intros; lra.
  exists (/m * PI); apply (is_RInt_gen_scal _ (/m) PI), integral_atan_comp_scal.
  easy.
exists (Rgt 0) (Rlt 0); try (exists 0; intros; psatzl R).
intros x y x0 y0; split; cbv [fst snd].
  intros z intz; unfold g.
  assert (0 < (z/m) ^ 2 + 1).
    apply Rplus_le_lt_0_compat; [apply pow2_ge_0 | psatzl R].
  split.
    now apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0, Rmult_lt_0_compat; lt0.
  rewrite <- !Rinv_mult_distr; try apply Rgt_not_eq; auto; cycle 1.
    now lt0.
  apply Rinv_le_contravar;[lt0 | ].
  rewrite <- (sqrt_pow2 (m * _)); cycle 1;[lt0 | ].
  apply sqrt_le_1_alt.
  rewrite Rmult_plus_distr_l Rmult_1_r Rmult_plus_distr_l.
  rewrite <- Rmult_assoc; replace (m * m * (z/m) ^2) with (z ^ 2); cycle 1.
    now field; apply Rgt_not_eq.
  assert (h : (z ^ 2 + m * m) ^ 2 = (z ^ 2 + m ^ 2) * (z ^ 2 + m ^ 2)) by ring.
  rewrite h; apply Rmult_le_compat;
    try (apply Rplus_le_le_0_compat; apply pow2_ge_0);
    apply Rplus_le_compat; auto with real;
    apply pow_incr; psatzl R.
(* Hard to admit that we have to do this. *)
apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
intros z _; apply (ex_derive_continuous (V := R_CompleteNormedModule)).
auto_derive.
assert (h : 0 < (z ^ 2 + a ^ 2) * (z ^ 2 + b ^ 2)).
  now apply Rmult_lt_0_compat; apply Rplus_le_lt_0_compat; try apply pow2_ge_0;
  apply pow2_gt_0; apply Rgt_not_eq.
now split;[exact h | split;[apply Rgt_not_eq, sqrt_lt_R0, h | ] ].
Qed.

Definition ell (a b : R) : R :=
  RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) .

Lemma ex_un_ell a b : 0 < a -> 0 < b ->
  exists ! v,
    is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) v.
Proof.
intros a0 b0.
(* Question: why do I have to apply Rbar_locally_filter? *)
apply ex_RInt_gen_unique; try apply Rbar_locally_filter.
now apply elliptic_integrable.
Qed.

Lemma is_RInt_gen_ell a b : 0 < a -> 0 < b ->
  is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) 
  (ell a b).
Proof.
now intros a0 b0; generalize (iota_correct _ (ex_un_ell a b a0 b0)).
Qed.

Lemma ell_unique a b v : 0 < a -> 0 < b ->
  is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) v ->
  v = ell a b.
Proof.
intros a0 b0 intv.
destruct (ex_RInt_gen_unique _ _ _ (ex_intro _ v intv)) as [w [_ Pw]].
now rewrite <- (Pw _ intv); apply Pw, is_RInt_gen_ell.
Qed.

Lemma scal_ell a b k : 0 < a -> 0 < b -> 0 < k ->
  ell (k * a) (k * b) = /k * ell a b.
Proof.
intros a0 b0 k0; assert (int_ellab := is_RInt_gen_ell _ _ a0 b0).
assert (ka0 : 0 < k * a) by now lt0.
assert (kb0 : 0 < k * b) by now lt0.
assert (int_ellk := is_RInt_gen_ell _ _ ka0 kb0).
assert (ellfq : filter_prod (Rbar_locally m_infty) (Rbar_locally p_infty)
          (fun p => forall x, Rmin (fst p) (snd p) < x < Rmax (fst p) (snd p) ->
              /k * (/k * ellf a b (/k * x + 0)) = ellf (k * a) (k * b) x)).
  apply filter_forall; intros _ x _; unfold ellf; symmetry.
  pattern x at 1 2; replace x with (k * (x / k)) by now field; apply Rgt_not_eq.
  (* I need to use the non-standard variant of rewrite. *)
  rewrite -> !Rpow_mult_distr, <-!Rmult_plus_distr_l, !Rmult_assoc.
  assert (help : forall v u w, u * (v * w) = v * (u * w)) by (intros; ring).
  rewrite (help (k ^ 2)) -(Rmult_assoc _ (k ^ 2)) sqrt_mult_alt;[ | lt0].
  rewrite <- Rpow_mult_distr, sqrt_pow2;[ | lt0].
  rewrite Rinv_mult_distr;[ | apply Rgt_not_eq; lt0 | lt0].
  rewrite Rplus_0_r (Rmult_comm (/k) x).
  now rewrite Rinv_mult_distr ?Rmult_assoc;[ | lt0 | lt0].
symmetry; apply ell_unique; auto.
apply (is_RInt_gen_ext _ _ _ ellfq).
apply (is_RInt_gen_scal (fun x => /k * ellf a b (/k * x + 0)) (/k)).
apply (is_RInt_gen_comp (ellf a b)).
  apply filter_forall; intros [x y] z _; split.
    apply (ex_derive_continuous (ellf a b)).
    now unfold ellf; auto_derive; repeat split; lt0.
  now split; [auto_derive;[ | field; lt0] | apply continuous_const].
apply (is_RInt_gen_filter_le (Rbar_locally m_infty) (Rbar_locally p_infty));
  try apply filtermap_filter; try apply Rbar_locally_filter; try easy.
  apply (filterlim_ext (fun x => /k * x));[intros; ring | ].
    apply (filterlim_ext (fun x => (fun p => fst p * snd p) (/k, x)));
      [ reflexivity | ].
    apply (filterlim_comp R (R * R) R (fun x => (/k, x))
             (fun p => fst p * snd p) (Rbar_locally m_infty)
             (filter_prod (locally (/k)) (Rbar_locally m_infty))).
      now apply filterlim_pair;[apply filterlim_const | apply filterlim_id].
    apply (filterlim_Rbar_mult (Finite (/k))).
  now apply is_Rbar_mult_sym, is_Rbar_mult_m_infty_pos, Rinv_0_lt_compat.
(* TODO : find a way to make this faster (and common with previous
   eight lines. *)
apply (filterlim_ext (fun x => /k * x));[intros; ring | ].
  apply (filterlim_ext (fun x => (fun p => fst p * snd p) (/k, x)));
    [ reflexivity | ].
  apply (filterlim_comp R (R * R) R (fun x => (/k, x))
           (fun p => fst p * snd p) (Rbar_locally p_infty)
           (filter_prod (locally (/k)) (Rbar_locally p_infty))).
    now apply filterlim_pair;[apply filterlim_const | apply filterlim_id].
  apply (filterlim_Rbar_mult (Finite (/k))).
now apply is_Rbar_mult_sym, is_Rbar_mult_p_infty_pos, Rinv_0_lt_compat.
Qed.

Ltac filterlim_tac :=
  apply filterlim_const || apply filterlim_id ||
  apply: filterlim_mult || apply: filterlim_plus || filterlim_tac.

Lemma ex_Rbar_plus_finite2 (a : Rbar) (b : R) :
  ex_Rbar_plus a b.
Proof.  now destruct a as [ a | | ].  Qed.

(* This is equation 13 in submitted paper "distant decimals of pi" *)
Lemma half_elliptic a b v1 v2 : 0 < a -> 0 < b ->
  is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) v1 ->
  is_RInt_gen (ellf a b) (at_point 0) (Rbar_locally p_infty) v2 ->
  v1 = 2 * v2.
Proof.
intros a0 b0 V pv2; symmetry; rewrite (ell_unique _ _ _ a0 b0 V); clear V.
enough (low : is_RInt_gen (ellf a b) (Rbar_locally m_infty) (at_point 0) v2).
  assert (whole := is_RInt_gen_Chasles _ _ _ _ low pv2).
  now rewrite -(ell_unique _ _ _ _ _ whole); auto; unfold plus; simpl; ring.
replace v2 with ((-1) * - v2) by ring.
apply is_RInt_gen_ext with (fun x => (-1) * (-1 * (ellf a b ((-1 * x) + 0)))).
  exists (Rgt 0) (fun x => x = 0).
      now exists 0; intros; auto.
    now apply refl_equal.
  intros x y _ _ z pz; unfold ellf.
  replace ((-1 * z + 0) ^ 2) with (z ^ 2) by  ring.
  change eq with (@eq R); ring.
apply (is_RInt_gen_scal _ (-1) (-v2)).
(* bug : here I need to use the ssreflect apply. *)
(* with plain apply I need (@is_RInt_gen_comp_lin R_NormedModule _ _ _ _). *)
apply (is_RInt_gen_comp (ellf a b)).
  apply filter_forall; intros [x y] z _; split.
    apply (ex_derive_continuous (ellf a b)).
    now unfold ellf; auto_derive; repeat split; lt0.
  now split; [auto_derive;[ | field; lt0] | apply continuous_const].
(* bug : here I need to use the ssreflect apply. *)
(* with plain apply I need (is_RInt_gen_swap (ellf a b)). *)
apply: is_RInt_gen_swap.
apply (is_RInt_gen_filter_le (at_point 0) (Rbar_locally p_infty) _ _ _ _); auto.
  enough (pl : is_lim (fun x => -1 * x + 0) 0 0).
    pattern 0 at 3; replace 0 with (-1 * 0 + 0) by ring.
    now intros S P; exact P.
  pattern 0 at 3; replace 0 with (-1 * 0 + 0) by ring.
  repeat (eapply is_lim_plus || eapply is_lim_mult || eapply is_lim_const || eapply is_lim_id
        || exact I).
  erewrite is_Rbar_mult_unique; [ | reflexivity]; reflexivity.
change (is_lim (fun x => -1 * x + 0) m_infty p_infty).
evar_last.
(* Two things to report : 1/ why does this command not do the rewrite with is_Rbar_mult
when possible ?
repeat (eapply is_lim_plus || eapply is_lim_mult || eapply is_lim_const || eapply is_lim_id
        || solve [cbn; psatzl R] || apply Rbar_plus_correct || apply ex_Rbar_plus_finite1
        || apply ex_Rbar_plus_finite2 || (erewrite is_Rbar_mult_unique; cycle 1). *)
(*2/ the following command raises an anomaly. *)
(* repeat (eapply is_lim_plus || eapply is_lim_mult || eapply is_lim_const || eapply is_lim_id
        || solve [cbn; psatzl R] || apply Rbar_plus_correct || apply ex_Rbar_plus_finite1
        || apply ex_Rbar_plus_finite2 || erewrite is_Rbar_mult_unique; cycle 1). *)
repeat (eapply is_lim_plus || eapply is_lim_mult || eapply is_lim_const || eapply is_lim_id
        || solve [cbn; psatzl R] || apply Rbar_plus_correct || apply ex_Rbar_plus_finite1
        || apply ex_Rbar_plus_finite2).
erewrite is_Rbar_mult_unique; cycle 1.
  solve [apply is_Rbar_mult_sym; apply is_Rbar_mult_m_infty_neg; unfold Rbar_lt; psatzl R|
       apply is_Rbar_mult_sym; apply is_Rbar_mult_m_infty_pos; unfold Rbar_lt; psatzl R |
       apply is_Rbar_mult_sym; apply is_Rbar_mult_p_infty_neg; unfold Rbar_lt; psatzl R|
       apply is_Rbar_mult_sym; apply is_Rbar_mult_p_infty_pos; unfold Rbar_lt; psatzl R |
       apply is_Rbar_mult_m_infty_neg; unfold Rbar_lt; psatzl R|
       apply is_Rbar_mult_m_infty_pos; unfold Rbar_lt; psatzl R |
       apply is_Rbar_mult_p_infty_neg; unfold Rbar_lt; psatzl R|
       apply is_Rbar_mult_p_infty_pos; unfold Rbar_lt; psatzl R].
reflexivity.
Qed. 

Fixpoint ag (a b : R) (n : nat) :=
  match n with 0 => (a, b) | S p => ag ((a + b)/2) (sqrt(a * b)) p end.

Definition a_ n x := fst (ag 1 x n).

Definition b_ n x := snd (ag 1 x n).

Lemma ag_step a b n : (ag a b (S n)) =
        ((fst (ag a b n) + snd (ag a b n)) / 2,
         sqrt (fst (ag a b n) * snd (ag a b n))).
Proof.
revert a b; induction n as [ | n IHn]; auto.
now intros a b; simpl; rewrite <- IHn; simpl.
Qed.

Lemma a_step n x : a_ (S n) x = (a_ n x + b_ n x) / 2.
Proof. now unfold a_, b_; rewrite ag_step. Qed.

Lemma b_step n x : b_ (S n) x = sqrt (a_ n x * b_ n x).
Proof. now unfold a_, b_; rewrite ag_step. Qed.

Definition M a b : R :=
  iota (fun v => filterlim (fun n =>fst (ag a b n)) Hierarchy.eventually
                    (locally v)).

Lemma ag_swap a b n : 0 < a -> 0 < b -> (0 < n)%nat ->
  ag a b n = ag b a n.
Proof.
now destruct n as [|n];[lia| simpl; rewrite -> Rplus_comm, Rmult_comm].
Qed.

Lemma pow_incr_inv x y n: 0 < x -> 0 < y -> x ^ S n <= y ^ S n -> x <= y.
Proof.
intros x0 y0 pxy.
destruct (Rle_lt_dec x y) as [xy | yx];auto.
assert (y ^ S n < x ^ S n); [ | psatzl R].
apply Rle_lt_trans with (y * x ^ n).
  simpl; apply Rmult_le_compat_l; try psatzl R.
  now apply pow_incr; psatzl R.
now simpl; apply Rmult_lt_compat_r; auto; apply pow_lt.
Qed.

Lemma ag_le' n a b : 0 < a -> 0 < b -> b <= a ->
  snd (ag a b n) <= snd (ag a b (S n)) /\
  snd (ag a b (S n)) <= fst (ag a b (S n)) /\
  fst (ag a b (S n)) <= fst (ag a b n).
Proof.
revert a b; induction n as [|n IHn]; intros a b a0 b0 ba;
  (assert (ar0 : 0 < (a + b) / 2) by psatzl R;
  assert (ge0 : 0 < sqrt (a * b)) by lt0;
  assert (arge : sqrt (a * b) <= (a + b) / 2);[
  apply (pow_incr_inv _ _ 1); try lt0;
  rewrite -> Rminus_le_0, sqrt_pow_2; try lt0;
  replace (((a + b) / 2) ^ 2 - a * b) with (((a - b) / 2) ^ 2) by field;
  now apply pow2_ge_0 | ]).
  simpl; split;[ | split;[easy | psatzl R ]].
  apply (pow_incr_inv _ _ 1); auto; rewrite sqrt_pow_2; try lt0.
  now simpl; rewrite Rmult_1_r; apply Rmult_le_compat_r; lt0.
simpl; apply (IHn _ _ ar0 ge0 arge).
Qed.

Lemma ag_le n a b : 0 < a -> 0 < b -> b <= a ->
  b <= snd (ag a b n) /\
  snd (ag a b n) <= fst (ag a b n) /\
  fst (ag a b n) <= a.
Proof.
revert a b; induction n.
  now simpl; intros; psatzl R.
intros a b a0 b0 ba.
destruct (ag_le' 0 _ _ a0 b0 ba) as [bbn [bnan ana]]; simpl in bbn, bnan, ana.
assert (ar0 : 0 < (a + b) / 2) by psatzl R.
assert (ge0 : 0 < sqrt (a * b)) by lt0.
destruct (IHn _ _ ar0 ge0 bnan) as [IHn1 [IHn2 IHn3]].
split; [apply Rle_trans with (1 := bbn); exact IHn1 | ].
split; [exact IHn2 | ].
apply Rle_trans with (2 := ana); exact IHn3.
Qed.

Lemma ag_shift n m a b : ag a b (n + m) = ag (fst (ag a b m)) (snd (ag a b m)) n.
Proof.
revert n a b; induction m.
  now intros; rewrite Nat.add_0_r.
now intros n a b; rewrite Nat.add_succ_r; simpl; apply IHm.
Qed.

Lemma fst_ag_decrease n p a b :(1 <= n <= p)%nat -> 0 < a -> 0 < b -> b <= a ->
 fst (ag a b p) <= fst (ag a b n).
Proof.
intros n1p a0 b0 bla.
replace p with ((p - n) + n)%nat by lia.
rewrite ag_shift.
destruct (ag_le n a b); try lt0.
destruct (ag_le (p - n) (fst (ag a b n)) (snd (ag a b n))); lt0.
Qed.

Lemma snd_ag_grow n p a b :(1 <= n <= p)%nat -> 0 < a -> 0 < b -> b <= a ->
 snd (ag a b n) <= snd (ag a b p).
Proof.
intros n1p a0 b0 bla.
replace p with ((p - n) + n)%nat by lia.
rewrite ag_shift.
destruct (ag_le n a b); try lt0.
destruct (ag_le (p - n) (fst (ag a b n)) (snd (ag a b n))); lt0.
Qed.

Lemma ex_lim_agm a b : 0 < a -> 0 < b ->
  ex_finite_lim_seq (fun n => (fst (ag a b n))).
Proof.
enough (gen : forall a b, 0 < a -> 0 < b -> b <= a ->
          ex_finite_lim_seq (fun n => fst (ag a b n))).
  intros a0 b0; destruct (Rle_dec b a) as [ba | ab].
    now apply gen.
  assert (swap : ex_finite_lim_seq (fun n => fst (ag b a n))).
    now apply gen; auto; psatzl R.
  destruct swap as [l A]; exists l.
  apply (is_lim_seq_ext_loc (fun n => fst (ag b a n))); auto.
  now exists 1%nat; intros; rewrite ag_swap; auto.
clear a b; intros a b a0 b0 ba.
apply (ex_finite_lim_seq_decr _ b).
  intros n; destruct (ag_le' n a b a0 b0 ba) as [_ [_ it]]; assumption.
intros n; revert a b a0 b0 ba; induction n as [ | n IHn].
  now simpl; auto.
simpl; intros a b a0 b0 ba.
destruct (ag_le' 0 a b a0 b0 ba) as [cmp1 [cmp2 cmp3]]; simpl in cmp1, cmp2, cmp3.
now apply Rle_trans with (1 := cmp1), IHn; lt0.
Qed.

Lemma agm_diff a b : 0 < a -> 0 < b ->
  (a + b) / 2 - sqrt (a * b) = (a - b) ^ 2 /(4 * ((a + b) / 2 + sqrt (a * b))).
Proof.
intros a0 b0.
replace ((a + b) / 2 - sqrt (a * b)) with
  ((((a + b) / 2) ^ 2 - sqrt (a * b) ^ 2) / ((a + b)/2 + sqrt (a * b)))
  by (field; lt0).
replace (sqrt (a * b) ^ 2) with (a * b) by (rewrite sqrt_pow_2; lt0).
now field; lt0.
Qed.

Lemma agm_conv a b n : 0 < a -> 0 < b -> b <= a ->
  fst (ag a b n) - snd (ag a b n) <= (a - b) / (2 ^ n).
Proof.
revert a b; induction n as [ | n IHn].
  now simpl; intros; psatzl R.
intros a b a0 b0 ba; simpl.
assert (t := ag_le 1 a b a0 b0 ba); simpl in t; destruct t as [bsq [ga ara]].
apply Rle_trans with (((a + b) / 2  - sqrt (a * b)) / 2 ^ n);[apply IHn; lt0 | ].
rewrite agm_diff; try lt0.
replace ((a - b) / (2 * 2 ^ n)) with (((a - b) / 2 ^ n) * /2) by (field; lt0).
replace ((a - b) ^ 2 / (4 * ((a + b) / 2 + sqrt (a * b))) / 2 ^ n) with
        (((a - b) / 2 ^ n) * (/ (4 * ((a + b) / 2 + sqrt (a * b))) * (a - b)))
  by (field; repeat split; lt0).
apply Rmult_le_compat_l;[apply Rmult_le_pos; lt0| ].
apply Rle_trans with (/(4 * ((a + b) / 2 + sqrt (a * b))) *
      (2 * (((a + b) / 2 + sqrt (a * b))))).
  now apply Rmult_le_compat_l; lt0.
now apply Req_le; field; lt0.
Qed.

Lemma is_lim_seq_M a b : 0 < a -> 0 < b ->
   is_lim_seq (fun n => fst (ag a b n)) (M a b).
Proof.
intros a0 b0; unfold M, is_lim_seq.
match goal with |- context[iota ?x] => apply (iota_correct x) end.
destruct (ex_lim_agm _ _ a0 b0) as [v Pv]; exists v; split.
  now apply Pv.
intros x' Px'; apply (filterlim_locally_unique _ v x' Pv Px').
Qed.

Lemma is_lim_seq_finite_unique :
  forall {f} (l1 l2 : R), is_lim_seq f l1 -> is_lim_seq f l2 -> l1 = l2.
Proof.
intros f l1 l2 A B.
assert (t := is_lim_seq_unique _ _ A); rewrite (is_lim_seq_unique _ _ B) in t.
now injection t.
Qed.

Lemma variable_change_for_agm : forall s t a b, 0 < t -> 0 < a -> 0 < b ->
 s = ((t - a * b /t) /2) ->
 4 * (s ^ 2 + ((a + b) / 2) ^ 2) * (s ^ 2 + a * b) /
  ((1 + a * b / t ^ 2) / 2) ^ 2 =
 (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2).
Proof. intros s t a b t0 a0 b0 q; rewrite q; field; split; lt0. Qed.

Local Lemma var_change_lim_p_infty a : 0 < a ->
  is_lim (fun x => (x - a/x)/2) p_infty p_infty.
  replace p_infty with (Rbar_div (Rbar_plus p_infty
                          (Rbar_opp (Rbar_div a p_infty))) 2) at 2.
Proof.
assert (Finite 2 <> Finite 0) by (intros ij; injection ij; psatzl R).
assert (is_lim (fun _ => 2) p_infty 2) by apply is_lim_const.
intros a0; apply is_lim_div; auto.
    evar_last.
      eapply is_lim_minus.
          now eapply is_lim_id.
        eapply is_lim_div; auto.
              now eapply is_lim_const.
            now eapply is_lim_id.
          discriminate.
        exact I.
      unfold is_Rbar_minus; simpl; rewrite -> Rmult_0_r, Ropp_0.
      now apply Rbar_plus_correct; exact I.
    reflexivity.
  now simpl; lt0.
simpl; case (Rle_dec 0 (/2)); try psatzl R.
intros r; case (Rle_lt_or_eq_dec _ _ r); try reflexivity; psatzl R.
Qed.

Local Lemma filterlim_var_change_0 a : 0 < a ->
  filterlim (fun x => (x - a / x) / 2) (at_right 0) (Rbar_locally m_infty).
Proof.
intros a0; assert (Finite 2 <> 0) by (intros ij; injection ij; psatzl R).
replace m_infty with
  (Rbar_mult (Rbar_plus 0 (Rbar_opp (Rbar_mult a p_infty))) (/2));
  cycle 1.
  simpl.
  destruct (Rle_dec 0 a) as [ag0 | al0];[ | psatzl R].
  destruct (Rle_lt_or_eq_dec 0 a ag0);[ | psatzl R].
  simpl; destruct (Rle_dec 0 (/2)) as [v20 | v20];[ | psatzl R].
  now destruct (Rle_lt_or_eq_dec 0 (/2) v20);[ | psatzl R].
apply (filterlim_comp _ _ _ (fun x => x - a / x) (fun x => x / 2)
        _ (Rbar_locally (Rbar_plus 0 (Rbar_opp (Rbar_mult a p_infty))))); cycle 1.
  apply filterlim_Rbar_mult_r.
apply (@filterlim_comp_2 R R R R (at_right 0) (at_right 0) (Rbar_locally (Rbar_opp (Rbar_mult a p_infty)))
           _ _ (fun x => x) (fun x => -(a / x)) Rplus).
    now apply filterlim_id.
  apply (@filterlim_comp _ _ _ (fun x => a / x) Ropp _
                (Rbar_locally (Rbar_mult a p_infty))).
  apply (@filterlim_comp_2 R R R R (at_right 0) (Rbar_locally a)
      (Rbar_locally p_infty) (Rbar_locally (Rbar_mult a p_infty)) _
      (fun _ => a) Rinv (fun x y => x * y)).
        now apply filterlim_const.
      now apply filterlim_Rinv_0_right.
    apply filterlim_Rbar_mult.
    now apply Rbar_mult_correct; simpl; lt0.
  now apply filterlim_Rbar_opp.
assert (fle : filter_le       (filter_prod (at_right 0)
         (Rbar_locally (Rbar_opp (Rbar_mult a p_infty))))
      (filter_prod (Rbar_locally 0)
         (Rbar_locally (Rbar_opp (Rbar_mult a p_infty))))).
  apply filter_prod_le; cycle 1.
    now apply filter_le_refl.
  now unfold at_right; apply filter_le_within.
apply (filterlim_filter_le_1 _ fle).
apply filterlim_Rbar_plus.
apply Rbar_plus_correct; simpl.
destruct (Rle_dec 0 a) as [ag0 |al0];[|psatzl R].
destruct (Rle_lt_or_eq_dec 0 a ag0); easy.
Qed.

(* This is equation 14 in submitted version of "distant decimals of pi" *)
Lemma elliptic_agm_step a b c d (v : R) : 0 < a -> 0 < b ->
  c = (a + b)/2 -> d = sqrt(a * b) ->
  is_RInt_gen (fun x => /sqrt((x ^ 2 + c ^ 2) * (x ^ 2 + d ^ 2)))
      (Rbar_locally m_infty) (Rbar_locally p_infty) v ->
  is_RInt_gen (fun x => /sqrt((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))
      (Rbar_locally m_infty) (Rbar_locally p_infty) v.
Proof.
intros a0 b0 ceq deq vp.
assert (c0 : 0 < c) by psatzl R.
assert (d0 : 0 < d) by (rewrite deq; lt0).
destruct (ex_un_ell a b) as [w [wp wq]]; auto; simpl in w; move w before v.
destruct (ex_RInt_gen_cut 0 _ _ _ 
   (filter_Rlt_m_infty_at_point 0) (filter_Rlt_at_point_p_infty _)
    (ex_intro _ w wp)) as [w2 w2p].
set (s x := (x - a * b/x)  /2).
set (s' x := (1 + (a * b) / x ^ 2) / 2).
enough (half : is_RInt_gen (ellf a b)
                  (at_point 0) (Rbar_locally p_infty) (v/2)).
  assert (wv2 := half_elliptic _ _ w (v/2) a0 b0 wp half).
  replace v with (2 * (v / 2)) by field; rewrite <- wv2; assumption.
apply: is_RInt_gen_at_right_at_point.
  apply filter_forall; intros x; apply: ex_derive_continuous; unfold ellf.
  now auto_derive; repeat rewrite -> !Rmult_0_l, !Rplus_0_l; repeat split; lt0.
apply (is_RInt_gen_ext (fun x => / 2 * (s' x * ellf c d (s x)))).
  exists (Rlt 0) (Rlt 0).
      now exists (mkposreal _ Rlt_0_1); intros; psatzl R.
    now exists 0; intros; psatzl R.
  simpl; intros x y x0 y0 z cz; unfold ellf, s, s'.
  assert (z0 : 0 < z).
    now apply Rlt_trans with (Rmin x y);[apply Rmin_pos | psatzl R].
  rewrite -[(_ + _)/2]sqrt_square;[ | lt0].
  assert (s2 : sqrt 4 = 2) by (rewrite sqrt_square; lt0).
  rewrite <-s2 at 1.
  rewrite -> ! inv_sqrt, <- !sqrt_mult_alt; try lt0.
  apply f_equal.
  assert (clean_sqrt : sqrt (a * b) ^ 2 = a * b).
    now simpl; rewrite -> Rmult_1_r, sqrt_sqrt; auto; lt0.
  rewrite <- (variable_change_for_agm ((z - a * b / z)/2) z), ceq, deq; try lt0.
  rewrite clean_sqrt.
  field; repeat split; try lt0.
  now rewrite <- !Rmult_assoc, <- !Rmult_plus_distr_r; apply Rgt_not_eq; lt0.
replace (v / 2) with (/2 * v) by field.
apply: is_RInt_gen_scal.
apply is_RInt_gen_comp.
  exists (Rlt 0) (Rlt 0).
      now exists (mkposreal _ Rlt_0_1); intros; psatzl R.
    now exists 0; intros; psatzl R.
  simpl; intros x y x0 y0 z cz.
  assert (0 < z).
    now apply Rlt_le_trans with (Rmin x y); [apply Rmin_pos | psatzl R].
  split.
    now apply: ex_derive_continuous; unfold ellf; auto_derive; repeat split; lt0.
  split.
    now unfold s, s'; auto_derive;[| field]; lt0.
  now apply: ex_derive_continuous; unfold s'; auto_derive; lt0.
apply: (is_RInt_gen_filter_le (Rbar_locally m_infty) (Rbar_locally p_infty)).
    now unfold s; apply filterlim_var_change_0; lt0.
  now apply var_change_lim_p_infty; lt0.
assumption.
Qed.

Lemma ell_ag_n n a b : 0 < a -> 0 < b ->
   ell a b = ell (fst (ag a b n)) (snd (ag a b n)).
Proof.
revert a b; induction n;[easy | ].
intros a b a0 b0.
assert (ar0 : 0 < (a + b) / 2) by lt0.
assert (ge0 : 0 < sqrt (a * b)) by lt0.
simpl; transitivity (ell ((a + b) / 2) (sqrt (a * b)));[ |now apply IHn].
unfold ell.
destruct (ex_un_ell a b a0 b0) as [ww [Pww _]].
destruct (ex_un_ell _ _ ar0 ge0) as [ww' [Pww' _]].
rewrite -> (is_RInt_gen_unique _ _ Pww').
apply (elliptic_agm_step a b) in Pww'; auto.
unfold ellf.
now rewrite -> (is_RInt_gen_unique _ _ Pww').
Qed.

(* This is equation 16 in submitted version of "distant decimals of pi" *)
Lemma quarter_elliptic x : 0 < x -> ell 1 x = 4 * RInt (ellf 1 x) 0 (sqrt x).
Proof.
intros x0.
set (Pv := is_RInt_gen_ell 1 x Rlt_0_1 x0).
destruct (ex_RInt_gen_cut 0 _ _
          (ellf 1 x) 
          (filter_Rlt_m_infty_at_point _) (filter_Rlt_at_point_p_infty _)
               (ex_intro _ _ Pv)) as [v2 Pv2]; simpl in v2.
assert (0 < sqrt x) by lt0.
assert (m0x : filter_Rlt (at_point 0) (at_point (sqrt x)))
  by now apply filter_Rlt_at_point.
assert (mxp : filter_Rlt (at_point (sqrt x)) (Rbar_locally p_infty)).
  now apply filter_Rlt_at_point_p_infty.
destruct (ex_RInt_gen_cut (sqrt x) (at_point 0) _ (ellf 1 x) m0x mxp
             (ex_intro _ _ Pv2)) as [v3 Pv3].
assert (ex_RInt (ellf 1 x) 0 (sqrt x)) as [v4 Pv4].
  apply: ex_RInt_continuous; intros z _; unfold ellf.
  now apply: ex_derive_continuous; auto_derive; repeat split; lt0.
assert (Pv4' := Pv4).
rewrite <- is_RInt_gen_at_point in Pv4.
assert (sum := is_RInt_gen_Chasles _ _ _ _ Pv4 Pv3).
destruct (ex_RInt_gen_unique _ _ _ (ex_intro _ _ Pv2)) as [w [Pw qw]].
rewrite (half_elliptic _ _ _ _ Rlt_0_1 x0 Pv sum).
rewrite (is_RInt_unique _ _ _ _ Pv4').
assert (v3_4 :is_RInt_gen (ellf 1 x) (at_point 0) (at_point (sqrt x)) v3).
  apply: is_RInt_gen_at_right_at_point.
    apply filter_forall; simpl; unfold ellf; intros; apply: ex_derive_continuous.
    now auto_derive; repeat split; lt0.
  apply (is_RInt_gen_ext (fun t => - (- (x / t ^ 2) *
            ellf 1 x (x / t)))).
    exists (Rlt 0) (eq (sqrt x)).
        now exists (mkposreal _ Rlt_0_1); simpl; intros; tauto.
      now unfold at_point.
    intros a b a0 bq z pz; simpl in pz.
    assert (0 < b) by (rewrite <- bq; lt0).
    assert (0 < z).
      apply Rlt_trans with (Rmin a b); try tauto.
      now apply Rmin_glb_lt; lt0.
    unfold ellf; rewrite -> Ropp_mult_distr_l, Ropp_involutive.
    replace (x / z ^ 2) with (/ sqrt ((z ^ 2) ^ 2 / (x ^ 2)));
        cycle 1.
      rewrite -> sqrt_div_alt, !sqrt_pow2; try lt0.
      now field; split; lt0.
    rewrite <- Rinv_mult_distr; try lt0.
    rewrite <- sqrt_mult; try lt0.
    apply f_equal with (f := fun x => / sqrt x).
    now field; lt0.
  rewrite <- (Ropp_involutive v3).
  apply/is_RInt_gen_swap/is_RInt_gen_opp.
  apply: (is_RInt_gen_comp (ellf 1 x) (fun u => - (x / u ^ 2))
                           (fun u => x / u)).
    exists (eq (sqrt x)) (Rlt 0).
        now unfold at_point.
      now exists (mkposreal _ Rlt_0_1); tauto.
    simpl; intros a b qa b0 y py.
    assert (0 < y).
      now apply Rlt_le_trans with (Rmin a b);lt0.
    split.
      now apply: ex_derive_continuous; unfold ellf; auto_derive;
        repeat split; lt0.
    split.
      auto_derive; try field; lt0.
    apply: ex_derive_continuous; auto_derive; lt0.
  apply: (is_RInt_gen_filter_le _ _ _ _ _ _ _ _ Pv3).
    intros A B; unfold filtermap, at_point; unfold at_point in B.
    enough (tmp : x / sqrt x = sqrt x) by now rewrite tmp.
    now rewrite <- (sqrt_pow_2 x) at 1; try lt0; field; lt0.
  apply: (filterlim_comp_2 (G := locally x)(H := Rbar_locally p_infty)
              (fun _ => x) (fun u => / u)
            (fun a b => a * b)).
      now apply filterlim_const.
    now apply filterlim_Rinv_0_right.
  apply (filterlim_Rbar_mult x p_infty p_infty).
  apply is_Rbar_mult_sym, is_Rbar_mult_p_infty_pos; simpl; psatzl R.
destruct (ex_RInt_gen_unique _ _ _ (ex_intro _ _ Pv4)) as [w' [_ qw']].
now rewrite <- (qw' _ Pv4), <- (qw' _ v3_4); unfold plus; simpl; ring.
Qed.

Lemma ell_lower_bound a b : 0 < a -> 0 < b ->
  PI / Rmax a b <= ell a b.
Proof.
assert (p0 : 0 < PI) by exact PI_RGT_0.
intros a0 b0.
assert (m0 : 0 < Rmax a b) by (apply (Rlt_le_trans _ _ _ a0), Rmax_l).
replace (PI / Rmax a b) with (ell (Rmax a b) (Rmax a b)).
  unfold ell.
  apply (is_RInt_gen_Rle (ellf a b) _ (ellf (Rmax a b) (Rmax a b)) _
          (Rbar_locally m_infty) (Rbar_locally p_infty)); auto.
        now apply filter_Rlt_m_infty_p_infty.
      now apply is_RInt_gen_ell.
    now apply is_RInt_gen_ell.
  apply filter_forall; intros p x _; clear p.
  apply Rle_Rinv; try lt0.
  apply sqrt_le_1_alt; try lt0.
  apply Rmult_le_compat; try lt0.
    now apply Rplus_le_compat_l, pow_incr; split;[lt0 | apply Rmax_l].
  now apply Rplus_le_compat_l, pow_incr; split;[lt0 | apply Rmax_r].
assert (fact1 :
      is_RInt_gen (fun x => / Rmax a b * (/ Rmax a b * /((x / Rmax a b) ^ 2 + 1)))
             (Rbar_locally m_infty)
             (Rbar_locally p_infty) (ell (Rmax a b) (Rmax a b))).
  apply (is_RInt_gen_ext (ellf (Rmax a b) (Rmax a b))); auto.
    apply filter_forall; intros p x _; clear p.
    unfold ellf; rewrite sqrt_square; field_simplify; auto.
        split; lt0.
      lt0.
    unfold Rdiv at 1; rewrite Rmult_0_l; lt0.
  now apply is_RInt_gen_ell.
assert (fact2 : is_RInt_gen (fun x =>
                       /Rmax a b * (/Rmax a b * /((x /Rmax a b ) ^ 2 + 1)))
            (Rbar_locally m_infty) (Rbar_locally p_infty) (/Rmax a b * PI)).
  now apply/is_RInt_gen_scal/integral_atan_comp_scal.
rewrite <- (is_RInt_gen_unique _ _ fact1), (is_RInt_gen_unique _ _ fact2).
now rewrite Rmult_comm.
Qed.

Lemma ell_upper_bound a b : 0 < a -> 0 < b ->
  ell a b <= PI / Rmin a b.
Proof.
assert (p0 : 0 < PI) by exact PI_RGT_0.
intros a0 b0.
assert (m0 : 0 < Rmin a b) by now apply Rmin_glb_lt.
replace (PI / Rmin a b) with (ell (Rmin a b) (Rmin a b)).
  unfold ell.
  generalize (iota_correct _ (ex_un_ell _ _ m0 m0)).
  set (elm := iota _); intros iselm.
  generalize (iota_correct _ (ex_un_ell _ _ a0 b0)).
  set (ela := iota _); intros isela.
  apply (is_RInt_gen_Rle (ellf (Rmin a b) (Rmin a b)) _ (ellf a b) _
          (Rbar_locally m_infty) (Rbar_locally p_infty)); auto.
      now apply filter_Rlt_m_infty_p_infty.
  apply filter_forall; intros p x _; clear p.
  apply Rle_Rinv; try lt0.
  apply sqrt_le_1_alt; try lt0.
  apply Rmult_le_compat; try lt0.
    now apply Rplus_le_compat_l, pow_incr; split;[lt0 | apply Rmin_l].
  now apply Rplus_le_compat_l, pow_incr; split;[lt0 | apply Rmin_r].
assert (fact1 :
      is_RInt_gen (fun x => / Rmin a b * (/ Rmin a b * /((x / Rmin a b) ^ 2 + 1)))
             (Rbar_locally m_infty)
             (Rbar_locally p_infty) (ell (Rmin a b) (Rmin a b))).
apply (is_RInt_gen_ext (ellf (Rmin a b) (Rmin a b))); auto.
  apply filter_forall; intros p x _; clear p.
  unfold ellf; rewrite sqrt_square; field_simplify; auto.
      split; lt0.
    lt0.
  unfold Rdiv at 1; rewrite Rmult_0_l; lt0.
now apply is_RInt_gen_ell.
assert (fact2 : is_RInt_gen (fun x =>
                       /Rmin a b * (/Rmin a b * /((x /Rmin a b ) ^ 2 + 1)))
            (Rbar_locally m_infty) (Rbar_locally p_infty) (/Rmin a b * PI)).
  now apply/is_RInt_gen_scal/integral_atan_comp_scal.
rewrite <- (is_RInt_gen_unique _ _ fact1), (is_RInt_gen_unique _ _ fact2).
now rewrite Rmult_comm.
Qed.

Lemma div_pow2_le x n : 0 <= x -> x / 2 ^ n <= x.
Proof.
intros x0; induction n.
  now replace (x / 2 ^ 0) with x by field; psatzl R.
replace (x / 2 ^ S n) with ((x / 2 ^ n) / 2) by (simpl; field; lt0).
psatzl R.
Qed.

Lemma M_swap a b : 0 < a -> 0 < b -> M a b = M b a.
Proof.
intros a0 b0.
apply (is_lim_seq_finite_unique _ _ (is_lim_seq_M _ _ a0 b0)).
apply (is_lim_seq_ext_loc (fun n => fst (ag b a n))).
  exists 1%nat; intros [ | k];[now intros abs; case (Nat.nle_succ_0 0) | ].
  now intros _; simpl; rewrite -> Rplus_comm, Rmult_comm.
now apply is_lim_seq_M.
Qed.

Lemma Mbounds a b : 0 < a -> 0 < b -> b <= a -> b <= M a b <= a.
Proof.
intros a0 b0 amb.
assert (Pm := is_lim_seq_M _ _ a0 b0).
assert (M_is_lim := is_lim_seq_unique _ _ Pm).
split.
  assert (limb : Lim_seq (fun _ => b) = b) by apply Lim_seq_const.
  change (Rbar_le (Finite b) (Finite (M a b))).
  rewrite <- limb, <- M_is_lim.
  apply (Lim_seq_le_loc (fun _ => b) (fun n => fst (ag a b n))).
  apply filter_forall; intros n.
  destruct (ag_le n _ _ a0 b0 amb); psatzl R.
assert (lima : Lim_seq (fun _ => a) = a) by apply Lim_seq_const.
change (Rbar_le (Finite (M a b)) (Finite a)).
rewrite <- lima, <- M_is_lim.
apply (Lim_seq_le_loc (fun n => fst (ag a b n)) (fun _ => a)).
apply filter_forall; intros n.
destruct (ag_le n _ _ a0 b0 amb); psatzl R.
Qed.

Lemma M0 a b : 0 < a -> 0 < b -> 0 < M a b.
Proof.
revert a b; enough (main : forall a b, 0 < a -> 0 < b -> b <= a -> 0 < M a b).
  intros a b a0 b0; destruct (Rle_dec b a).
    now apply main.
  now rewrite M_swap; auto; apply main; auto; psatzl R.
intros a b a0 b0 amb; apply Rlt_le_trans with (1 := b0).
now destruct (Mbounds a b a0 b0 amb).
Qed.

Lemma ell0 a b : 0 < a -> 0 < b -> 0 < ell a b.
Proof.
intros a0 b0. apply Rlt_le_trans with (2 := ell_lower_bound _ _ a0 b0).
apply Rmult_lt_0_compat; try lt0.
apply Rinv_0_lt_compat; try lt0.
now apply Rlt_le_trans with (1 := a0), Rmax_l.
Qed.

Lemma M_shift a b n : 0 < a -> 0 < b ->
  M (fst (ag a b n)) (snd (ag a b n)) = M a b.
Proof.
revert a b.
assert (main : forall a b, 0 < a -> 0 < b -> b <= a ->
          M (fst (ag a b n)) (snd (ag a b n)) = M a b).
  intros a b a0 b0 ba.
  assert (t := is_lim_seq_unique _ _ (is_lim_seq_M _ _ a0 b0)).
  destruct (ag_le n a b); try lt0.
  assert (an0 : 0 < fst (ag a b n)) by lt0.
  assert (bn0 : 0 < snd (ag a b n)) by lt0.
  generalize (is_lim_seq_unique _ _ (is_lim_seq_M _ _ an0 bn0)).
  rewrite <- (Lim_seq_incr_n _ n) in t.
    rewrite <- (Lim_seq_ext (fun k => fst (ag a b (k + n)))), t.
    now intros q; injection q.
  now intros k; rewrite ag_shift.
intros a b a0 b0; destruct (Rle_dec b a).
  now apply main; lt0.
destruct (ag_le n b a); try lt0.
destruct n as [| p];[reflexivity |].
rewrite -> ag_swap, (M_swap a); try lt0; try lia.
now apply main; lt0.
Qed.

(* This is equation 15 in submitted version of "distant decimals of pi" *)
Lemma ell_agm a b : 0 < a -> 0 < b -> b <= a -> ell a b = PI / M a b.
Proof.
assert (pi0 : 0 < PI) by apply PI_RGT_0.
intros a0 b0 amb.
assert (ell a b = PI / (PI / ell a b) :> R).
  assert (ub := ell_lower_bound _ _ a0 b0).
  assert (0 < Rmax a b) by now apply Rlt_le_trans with (2 := Rmax_l _ _).
  assert (0 < PI / Rmax a b) by lt0.
  now symmetry; field; lt0.
enough (mablim : is_lim_seq (fun n => fst (ag a b n)) (Finite (PI/ell a b))).
  now rewrite (is_lim_seq_finite_unique _ _ (is_lim_seq_M _ _ a0 b0) mablim).
intros P [eps peps].
assert (exists n, (a - b) / 2 ^ n < eps) as [n Pn].
  destruct (Req_dec a b) as [ab | anb].
    now unfold Rdiv; exists 1%nat; rewrite -> ab, Rminus_eq_0, Rmult_0_l; lt0.
  assert (half_lt_1 : Rabs(/2) < 1) by (rewrite Rabs_right; lt0).
  assert (eps0 : 0 < eps / (a - b)) by (case eps; simpl; intros; lt0).
  destruct (pow_lt_1_zero (/2) half_lt_1 (eps / (a - b)) eps0) as [it Pit].
  exists it; apply Rmult_lt_reg_r with (/(a - b)); try lt0.
  unfold Rdiv; rewrite -> (Rmult_comm (a - b)), Rmult_assoc, Rinv_r; try lt0.
  apply Rle_lt_trans with (2 := Pit it (le_n _)).
  now rewrite -> Rmult_1_r, Rabs_right, Rinv_pow; try apply Rle_ge; lt0.
exists n; intros k nk; apply peps.
assert (cmps : b <= snd (ag a b k) /\ snd (ag a b k) <= fst (ag a b k) <= a).
  now apply ag_le.
assert (0 < fst (ag a b k) /\ 0 < snd (ag a b k)) as [an0 bn0].
  now split; psatzl R.
assert (ub := ell_lower_bound _ _ an0 bn0).
assert (lb := ell_upper_bound _ _ an0 bn0).
assert (mxv : Rmax (fst (ag a b k)) (snd (ag a b k)) = fst (ag a b k)).
  now rewrite Rmax_left; psatzl R.
assert (mnv : Rmin (fst (ag a b k)) (snd (ag a b k)) = snd (ag a b k)).
  now rewrite Rmin_right; psatzl R.
rewrite mxv in ub; rewrite mnv in lb.
set (p := (k - n)%nat); assert (kpn : k = (p + n)%nat)
 by now unfold p; rewrite Nat.sub_add.
change (Rabs (fst (ag a b k) - PI / ell a b) < eps).
rewrite Rabs_right; cycle 1.
  rewrite -> (ell_ag_n k _ _ a0 b0).
  apply Rle_ge, Rle_trans with (fst (ag a b k) - PI / (PI / fst (ag a b k))).
    now apply Req_le; field; lt0.
  apply Rplus_le_compat_l, Ropp_le_contravar, Rmult_le_compat_l; try lt0.
  clear -ub an0.
  now apply Rinv_le_contravar; lt0.
apply Rle_lt_trans with (fst (ag a b k) - snd (ag a b k)); cycle 1.
  apply Rle_lt_trans with (1 := agm_conv _ _ k a0 b0 amb).
  rewrite kpn; apply Rle_lt_trans with ((a - b) / 2 ^ n); auto.
  replace ((a - b) / 2 ^ (p + n)) with (((a - b) / 2 ^ n) / 2 ^ p); cycle 1.
    now rewrite pow_add; field; split; lt0.
  now apply div_pow2_le; apply Rmult_le_pos; lt0.
apply Rplus_le_compat_l, Ropp_le_contravar.
apply Rle_trans with (PI / (PI / snd (ag a b k))).
  now apply Req_le; field; split; lt0.
apply Rmult_le_compat_l; try lt0.
rewrite (ell_ag_n k _ _ a0 b0).
apply Rinv_le_contravar; try lt0.
clear -ub pi0 an0.
now apply Rlt_le_trans with (2 := ub); lt0.
Qed.

(* This is equation 10 in submitted version of "distant decimals of pi" *)
Lemma M_scal a b k : 0 < a -> 0 < b -> 0 < k -> M (k * a) (k * b) = k * M a b.
Proof.
assert (pi0 : 0 < PI) by apply PI_RGT_0.
revert a b; enough (main : forall a b, 0 < a -> 0 < b -> 0 < k -> b <= a ->
                      M (k * a) (k * b) = k * M a b).
  intros a b a0 b0 k0; destruct (Rle_lt_dec b a) as [ba | ab].
    now apply main.
  rewrite -> (M_swap (k * a)), (M_swap a); try lt0.
  now apply main; try lt0.
intros a b a0 b0 k0 ba.
replace (M (k * a) (k * b)) with (PI / ell (k * a) (k * b)).
  replace (M a b) with (PI / ell a b).
    rewrite scal_ell; try lt0; field; split; try lt0.
    now apply Rgt_not_eq, ell0.
  rewrite ell_agm; try lt0; field; split; try lt0.
  now apply Rgt_not_eq, M0.
rewrite ell_agm; try lt0; try (field; split;
                                 try lt0; apply Rgt_not_eq, M0; lt0).
now apply Rmult_le_compat_l; lt0.
Qed.

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

