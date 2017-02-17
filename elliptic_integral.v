Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

(* This is q2_1_2 in the original proof. *)
Local Lemma sin_cos_form_pos a b z:
   0 < a -> 0 < b -> 0 < a ^ 2 * cos z ^ 2 + b ^ 2 * sin z ^ 2.
Proof.
intros a0 b0; destruct (Req_dec (sin z) 0) as [sin0 | sinn0].
  assert (cos z ^ 2 = 1) as ->.
    simpl; rewrite Rmult_1_r; replace 1 with (1 - Rsqr (sin z)).
      now apply cos2.
    rewrite -> sin0, Rsqr_0; ring.
  rewrite -> sin0, Rmult_1_r, pow_ne_zero, Rmult_0_r, Rplus_0_r.
    now apply pow_lt.
  discriminate.
apply Rplus_le_lt_0_compat.
  now apply Rmult_le_pos; apply pow2_ge_0.
now apply Rmult_lt_0_compat; apply pow2_gt_0; auto; apply Rgt_not_eq.
Qed.

Ltac lt0 :=
  match goal with
  | |- _ => assumption
  | |- 0 < exp _ => apply exp_pos
  | |- 0 < pos _ => apply cond_pos
  | |- _ > 0 => unfold Rgt; lt0
  | |- 0 < 1 =>  apply Rlt_0_1
  | |- 0 < 2 => apply Rlt_0_2
  | |- 0 < PI => apply PI_RGT_0
  | |- _ <> 0 => apply Rgt_not_eq; lt0
  | |- 0 < Rabs _ + _ => apply (Rplus_le_lt_0_compat _ _ (Rabs_pos _)); lt0
  | |- 0 < _ * _ => apply Rmult_lt_0_compat; lt0
  | |- 0 < _ ^ 2 * cos _ ^ 2 + _ ^ 2 * sin _ ^ 2 => apply sin_cos_form_pos; lt0
  | |- 0 < (?a * (?a * 1)) * (cos ?z * (cos _ * 1)) +
           (?b * (?b * 1)) * (sin _ * (sin _ * 1)) =>
       apply (sin_cos_form_pos a b z); lt0
  | |- 0 < ?a * ?a * cos ?z * cos _ +
           ?b * ?b * sin _ * sin _ =>
       apply (sin_cos_form_pos a b z); lt0
  | |- 0 < _ + _ => apply Rplus_lt_0_compat; lt0
  | |- 0 < Rmin _ _ => apply Rmin_glb_lt; lt0
  | |- 0 < / _ => apply Rinv_0_lt_compat; lt0
  | |- 0 < sqrt _ => apply sqrt_lt_R0; lt0
  | |- 0 < _ / _ => unfold Rdiv; apply Rmult_lt_0_compat; lt0
  | |- 0 < _ ^ _ => apply pow_lt; lt0
  | |- 0 < _ ^ 2 + _ => apply Rplus_le_lt_0_compat;[apply pow2_ge_0 | lt0]
  | |- 0 < (?x * (?x * 1))%R + _ =>
                        apply Rplus_le_lt_0_compat;[apply pow2_ge_0 | lt0]
  | |- 0 <= Rabs _ => apply Rabs_pos
  | |- _ <= _ => apply Rlt_le; lt0
  | |- _ => psatzl R
  end.

(* TOD0 : move to standard. *)
Lemma sqrt_pow_2 x : 0 <= x -> sqrt x ^ 2 = x.
Proof. now intros x0; simpl; rewrite -> Rmult_1_r, sqrt_sqrt. Qed.

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
    apply filter_Rlt_witness with 0; exists 0; intros; fourier.
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

Definition ellf (a b : R) x := /sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)).

Definition ell (a b : R) :=
  iota (fun v => is_RInt_gen (ellf a b)
                   (Rbar_locally m_infty) (Rbar_locally p_infty) v).

(* This lemma could be for any normed module, but this requires
  that is_RInt_unique should also be for any normed module. *)
Lemma ex_RInt_gen_unique
  (F G : (R -> Prop) -> Prop) {FF : ProperFilter F}
  {FG : ProperFilter G} (f : R -> R) :
  ex_RInt_gen f F G -> exists ! v, is_RInt_gen f F G v.
Proof.
intros [v Pv]; exists v; split;[exact Pv | intros w [fw [w1 w2]]].
destruct Pv as [fv [v1 v2]].
apply ball_eq; intros eps.
assert (tw := w2 (ball w (pos_div_2 eps)) (locally_ball _ _)).
assert (tv := v2 (ball v (pos_div_2 eps)) (locally_ball _ _)).
(* Here it is annoying that I have to fix the filter to make it work. *)
destruct (filter_ex _
         (filter_and (F := filter_prod F G) _ _ tv
            (filter_and (F := filter_prod F G)_ _ tw
               (filter_and (F := filter_prod F G)_ _ v1 w1))))
   as [[c d] [b1 [b2 [i1 i2]]]]; simpl in i1, i2.
apply is_RInt_unique in i1; apply is_RInt_unique in i2.
assert (vw : fv (c,d) = fw (c, d)) by (rewrite <- i1; exact i2).
rewrite vw in b1.
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
now apply ball_triangle with (fw (c, d)); auto; apply ball_sym.
Qed.

Lemma ex_un_ell a b : 0 < a -> 0 < b ->
  exists ! v,
    is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) v.
Proof.
intros a0 b0.
(* Question: why do I have to apply Rbar_locally_filter? *)
apply ex_RInt_gen_unique; try apply Rbar_locally_filter.
now apply elliptic_integrable.
Qed.

Lemma filter_prod_le {T : Type} (F G F' G' : (T -> Prop) -> Prop) :
  filter_le F F' -> filter_le G G' -> filter_le (filter_prod F G)
    (filter_prod F' G').
Proof.  now intros FF GG S [S1 S2 FS GS Imp]; exists S1 S2; auto. Qed.

Lemma is_RInt_gen_filter_le {T : NormedModule R_AbsRing}
  F G F' G' {FF : Filter F} {FG : Filter G}
  {FF' : Filter F'} {FG' : Filter G'} (f : R -> T) v :
  filter_le F' F -> filter_le G' G -> is_RInt_gen f F G v ->
  is_RInt_gen f F' G' v.
Proof.
  intros lef leg [If [P1 P2]].
  exists If; split.
  now apply (filter_prod_le _ _ _ _ lef leg).
now apply filter_le_trans with (2 := P2); intros S; apply filter_prod_le.
Qed.

Lemma is_RInt_gen_comp {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa}
  {FFb : Filter Fb} (f : R -> R) (dg g : R -> R) l :
  filter_prod Fa Fb (fun p =>
      forall y, Rmin (fst p) (snd p) <= y <= Rmax (fst p) (snd p) ->
             continuous f (g y) /\
             is_derive g y (dg y) /\ continuous dg y) ->
  is_RInt_gen f (filtermap g Fa) (filtermap g Fb) l ->
  is_RInt_gen (fun x => scal (dg x) (f (g x))) Fa Fb l.
Proof.
intros dp [If [[S S' FS FS' fp1 fp2]]].
destruct dp as [S1 S2 FS1 FS2 dp].
exists (fun p => If(g (fst p), g (snd p))); split.
  exists (fun x => S (g x) /\ S1 x) (fun x => S' (g x) /\ S2 x);
      try now apply filter_and; auto.
  intros x y [sgx s1x] [sgy s2y]; simpl.
  replace (If(g x, g y)) with (RInt f (g x) (g y));
    [ | now apply is_RInt_unique, fp1].
  apply (is_RInt_comp f g dg).
    now intros z intz; apply (dp x y s1x s2y z intz).
  intros z intz; apply (dp x y s1x s2y z intz).
apply filter_le_trans with (2 := fp2).
now intros T [U V *]; exists (fun x => U (g x)) (fun x => V (g x)); auto.
Qed.

Lemma scal_ell a b k : 0 < a -> 0 < b -> 0 < k ->
  ell (k * a) (k * b) = /k * ell a b.
Proof.
intros a0 b0 k0.
generalize (iota_correct _ (ex_un_ell a b a0 b0)).
unfold ell at 2; set (v := iota _); intros intv.
assert (ka0 : 0 < k * a) by now lt0.
assert (kb0 : 0 < k * b) by now lt0.
generalize (iota_correct _ (ex_un_ell _ _ ka0 kb0)); unfold ell.
set (w := iota _); intros intw.
destruct (ex_un_ell (k * a) (k * b) ka0 kb0) as [ww [_ Pww]].
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
rewrite -(Pww _ intw).
enough (is_RInt_gen (ellf (k * a) (k * b)) (Rbar_locally m_infty)
          (Rbar_locally p_infty) (/k * v)) by now apply Pww.
apply (is_RInt_gen_ext _ _ _ ellfq).
apply (is_RInt_gen_scal (fun x => /k * ellf a b (/k * x + 0)) (/k)).
apply (is_RInt_gen_comp_lin (ellf a b)).
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

Lemma half_elliptic a b v1 v2 : 0 < a -> 0 < b ->
  is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty) v1 ->
  is_RInt_gen (ellf a b) (at_point 0) (Rbar_locally p_infty) v2 ->
  v1 = 2 * v2.
Proof.
intros a0 b0 pv1 pv2; destruct (ex_un_ell a b) as [w [p1 pw]]; auto.
assert (wv1 := pw _ pv1); rewrite <- wv1; clear pv1 wv1.
enough (low : is_RInt_gen (ellf a b) (Rbar_locally m_infty) (at_point 0) v2).
  assert (whole := is_RInt_gen_Chasles _ _ _ _ low pv2).
  rewrite (pw _ whole); unfold plus; simpl; ring.
replace v2 with ((-1) * - v2) by ring.
apply is_RInt_gen_ext with (fun x => (-1) * (-1 * (ellf a b ((-1 * x) + 0)))).
  exists (Rgt 0) (fun x => x = 0).
      now exists 0; intros; auto.
    now intros y py; apply ball_eq; intros z; apply ball_sym, py.
  intros x y _ _ z pz; unfold ellf.
  replace ((-1 * z + 0) ^ 2) with (z ^ 2) by  ring.
  (* bug : this should have been solved by ring. *)
  rewrite <- Rmult_assoc, <- Ropp_mult_distr_l, <- Ropp_mult_distr_r.
  now rewrite -> Ropp_involutive, !Rmult_1_l.
apply (is_RInt_gen_scal _ (-1) (-v2)).
(* bug : here I need to use the ssreflect apply. *)
(* with plain apply I need (@is_RInt_gen_comp_lin R_NormedModule _ _ _ _). *)
apply: is_RInt_gen_comp_lin.
(* bug : here I need to use the ssreflect apply. *)
(* with plain apply I need (is_RInt_gen_swap (ellf a b)). *)
apply: is_RInt_gen_swap.
apply (is_RInt_gen_filter_le (at_point 0) (Rbar_locally p_infty) _ _ _ _); auto.
  enough (pl : is_lim (fun x => -1 * x + 0) 0 0).
    pattern 0 at 3; replace 0 with (-1 * 0 + 0) by ring.
    now intros S P x px; rewrite <- (ball_eq _ _ px); apply P, ball_center.
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

Lemma ex_RInt_gen_cut (a : R) (F G: (R -> Prop) -> Prop)
   {FF : ProperFilter F} {FG : ProperFilter G} (f : R -> R) :
   filter_Rlt F G -> filter_Rlt F (at_point a) -> filter_Rlt (at_point a) G ->
   ex_RInt_gen f F G -> ex_RInt_gen f (at_point a) G.
Proof.
intros lFG lFa laG [l [g [ifg vfg]]].
set (v := R_complete_lim (filtermap (fun x => RInt f a x) G)).
exists v, (fun p => RInt f (fst p) (snd p)).
destruct laG as [m [S1 S2 p1 p2 laG]]; cbn in laG.
destruct ifg as [S3 S4 p3 p4 ifg].
destruct lFa as [m' [S5 S6 p5 p6 lFa]]; cbn in lFa.
assert (S6 a) by (apply p6, ball_center).
assert (S1 a) by (apply p1, ball_center).
split.
  exists (eq a) (fun y => S2 y /\ S4 y).
      now unfold at_point; intros; apply ball_eq.
    now apply filter_and; auto.
  simpl; intros x y <- ay; apply RInt_correct.
  destruct (filter_ex _ (filter_and _ _ p5 p3)).
  apply (ex_RInt_Chasles_2 f x);[split; apply Rlt_le;
     [destruct (lFa x a) | destruct(laG a y)]; (psatzl R || tauto) | ].
   exists (g(x, y)); apply ifg; tauto.
assert (t': forall eps : posreal, exists x,
         filtermap (fun x => RInt f a x) G (ball x eps)).
  intros eps.
  destruct (vfg (ball l (pos_div_2 eps)))
    as [S7 S8 p7 p8 vfg']; [now apply locally_ball |].
  destruct (filter_ex (F := G)
                (fun y => S8 y /\ S4 y /\ S2 y)) as [y Py].
    repeat apply filter_and; tauto.
  exists (RInt f a y); destruct (filter_ex (F := F)
                        (fun x => S7 x /\ S3 x /\ S5 x)) as [x Px].
    repeat apply filter_and; tauto.
  unfold filtermap; apply (filter_imp (fun y => S8 y /\ S4 y /\ S2 y)).
  intros z PZ; change (Rabs (RInt f a z - RInt f a y) < eps).
  replace (RInt f a z - RInt f a y) with
          ((RInt f x a + RInt f a z) - (RInt f x a + RInt f a y)) by ring.
    assert (ex_RInt f x y) by (exists (g(x, y)); apply ifg; tauto).
    assert (ex_RInt f x z) by (exists (g(x, z)); apply ifg; tauto).
    assert (x < a) by (destruct (lFa x a); psatzl R || tauto).
    assert (a < y) by (destruct (laG a y); psatzl R || tauto).
    assert (a < z) by (destruct (laG a z); psatzl R || tauto).
    assert (ex_RInt f x a).
      apply (ex_RInt_Chasles_1 f x a y);[psatzl R | assumption].
    rewrite !RInt_Chasles; auto;
       try (apply (ex_RInt_Chasles_2 f x); auto; psatzl R); cycle 1.
    change (ball (RInt f x y) eps (RInt f x z)).
    replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
    replace (RInt f x y) with (g(x, y))
      by (symmetry; apply is_RInt_unique, ifg; tauto).
    replace (RInt f x z) with (g(x, z))
      by (symmetry; apply is_RInt_unique, ifg; tauto).
    apply (ball_triangle _ l); [apply ball_sym | ]; apply vfg'; tauto.
  repeat apply filter_and; tauto.
intros P [eps Pe].
assert (t := (R_complete
            (filtermap (fun x => RInt f a x) G) _
            t' eps)).
apply (filter_imp (ball v eps)); [exact Pe | ].
(* This is way too clever for me to be satisfied. *)
apply: (Filter_prod (at_point a) G _ (eq a) _ _ t).
  now unfold at_point; apply: ball_eq.
intros x y <-; tauto.
Qed.

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

Lemma is_RInt_gen_at_point_at_right (f : R -> R) (a : R) F {FF : ProperFilter F}
  v : locally a (continuous f) -> is_RInt_gen f (at_point a) F v ->
  filter_Rlt (at_point a) F ->  is_RInt_gen f (at_right a) F v.
Proof.
intros [delta1 pd1] [inf [isinf limf]] [m [P Q FP FQ cmp]]; simpl in cmp.
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
destruct isinf as [P1 Q1 FP1 FQ1 isinf].
assert (pa : P a) by (apply FP; intros; apply ball_center).
exists (fun p => RInt f (fst p) (snd p)); split.
  exists (fun x => m > x /\ a < x) (fun x => Q x /\ Q1 x).
      destruct (filter_ex _ FQ) as [y Qy].
      destruct (cmp _ _ pa Qy).
      assert (ma : 0 < m - a) by psatzl R.
      exists (mkposreal _ ma); simpl; intros z; unfold ball; simpl.
      unfold AbsRing_ball, ball, minus, plus, opp, abs; simpl.
      now intros B az; revert B; rewrite Rabs_right; psatzl R.
    now apply filter_and.
  intros x y xm fq; simpl; apply RInt_correct.
  apply: (ex_RInt_Chasles_2 _ a).
    destruct (cmp a y pa); try tauto; psatzl R.
  exists (inf (a, y)); apply isinf; try tauto.
  now apply FP1; intros; apply ball_center.
intros P2 [eps P2eps].
set (M := Rabs (f a) + 1).
assert (M0 : 0 < eps / M) by (unfold M; lt0).
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a a').
  intros a' baa'.
  apply: ex_RInt_continuous; intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; cycle 1.
      psatzl Rdefinitions.R.
    apply Rle_lt_trans with (a' - a); try psatzl Rdefinitions.R.
    rewrite <- (Rabs_right (a' - a)); try psatzl Rdefinitions.R.
    tauto.
  change (Rabs (z - a) < delta1).
  destruct (Rle_dec a z) as [az | za].
    rewrite -> Rmin_right, Rmax_left in pz; try psatzl Rdefinitions.R.
    assert (za' : z = a) by psatzl Rdefinitions.R.
    now rewrite -> za', Rminus_eq_0, Rabs_R0; case delta1; tauto.
  rewrite -> Rmin_right, Rmax_left in pz; try psatzl Rdefinitions.R.
  rewrite Rabs_left; cycle 1.
  psatzl Rdefinitions.R.
  apply Rle_lt_trans with (a - a'); try psatzl Rdefinitions.R.
  rewrite <- (Rabs_right (a - a')); try psatzl Rdefinitions.R.
  now change (ball a' delta1 a); apply ball_sym; tauto.
destruct (limf (ball v (pos_div_2 eps))) as [Ql Rl FQl FRl vfi'].
  now apply locally_ball.
assert (pre_ep2 : 0 < eps / 2 * /M) by lt0.
set (ep2 := mkposreal _ pre_ep2).
assert (at_right a (fun x => ball a delta1 x /\ ball a ep2 x /\
                             ball a delta2 x /\ a < x /\ x < m)).
  repeat apply filter_and; try (now apply filter_le_within, locally_ball).
    now exists ep2; intros; tauto.
  destruct (filter_ex _ FQ) as [y' Py'].
  assert (ma0 : 0 < m - a).
    now destruct (cmp a y'); auto; psatzl R.
  exists (mkposreal _ ma0); simpl; intros y.
  intros bay ay; change (Rabs (y - a) < m - a) in bay.
  now rewrite -> Rabs_right in bay; psatzl R.
assert (F (fun y => Q y /\ Rl y /\ Q1 y)).
  now repeat apply filter_and; auto.
exists (fun x => ball a delta1 x /\ ball a ep2 x /\
                 ball a delta2 x /\ a < x /\ x < m)
          (fun y => Q y /\ Rl y /\ Q1 y); auto.
intros x y bx Ry; apply P2eps; simpl.
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
assert (Rabs (RInt f a x) < pos_div_2 eps).
  apply Rle_lt_trans with ((x - a) * M).
    apply abs_RInt_le_const;[apply Rlt_le; tauto | | ].
      now apply: exrint_close; tauto.
    intros t atx.
    replace (f t) with (f a + (f t - f a)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat;[apply Rle_refl | ].
    apply Rlt_le, (Pd2 t).
    change (Rabs (t - a) < delta2); rewrite Rabs_right;[ | psatzl R].
    apply Rle_lt_trans with (x - a);[psatzl R | ].
    now rewrite <- (Rabs_right (x - a));[tauto | psatzl R].
  replace (pos (pos_div_2 eps)) with (ep2 * M).
    rewrite <- (Rabs_right (x - a));[|psatzl R].
    now apply Rmult_lt_compat_r;[unfold M; lt0 | tauto].
  simpl; field; unfold M; lt0.
apply ball_triangle with (RInt f a y); cycle 1.
  change (Rabs (RInt f x y - RInt f a y) < pos_div_2 eps).
  replace (RInt f a y) with (RInt f a x + RInt f x y); cycle 1.
  apply RInt_Chasles.
      now apply: exrint_close; tauto.
    apply: (ex_RInt_Chasles_2 f a).
      split;[apply Rlt_le; tauto | apply Rlt_le, Rlt_trans with m; try tauto].
    now destruct (cmp a y); tauto.
  exists (inf (a, y)); apply isinf.
    now apply FP1; intros; apply ball_center.
  now tauto.
  now rewrite [_ - _](_ : _ = - RInt f a x) ?Rabs_Ropp;[ | ring].
rewrite (is_RInt_unique f a y (inf(a, y))); cycle 1.
  now apply isinf;[apply FP1; intros; apply ball_center | tauto].
now apply vfi';[apply FQl; intros; apply ball_center | tauto].
Qed.

Lemma is_RInt_gen_at_right_at_point (f : R -> R) (a : R) F {FF : ProperFilter F}
  v :
  locally a (continuous f) -> is_RInt_gen f (at_right a) F v ->
  is_RInt_gen f (at_point a) F v.
Proof.
intros [delta1 pd1].
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
intros [fi [ifi vfi]].
set (M := Rabs (f a) + 1).
assert (M0 : 0 < M) by (unfold M; lt0).
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
destruct ifi as [Q2 R2 FQ2 FR2 ifi].
assert (atrd1 : at_right a (ball a delta1)) by (exists delta1; tauto).
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a a').
  intros a' baa'.
  apply: ex_RInt_continuous; intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; cycle 1.
      psatzl Rdefinitions.R.
    apply Rle_lt_trans with (a' - a); try psatzl Rdefinitions.R.
    rewrite <- (Rabs_right (a' - a)); try psatzl Rdefinitions.R.
  tauto.
  change (Rabs (z - a) < delta1).
  destruct (Rle_dec a z) as [az | za].
    rewrite -> Rmin_right, Rmax_left in pz; try psatzl Rdefinitions.R.
    assert (za' : z = a) by psatzl Rdefinitions.R.
    now rewrite -> za', Rminus_eq_0, Rabs_R0; case delta1; tauto.
  rewrite -> Rmin_right, Rmax_left in pz; try psatzl Rdefinitions.R.
  rewrite Rabs_left; cycle 1.
  psatzl Rdefinitions.R.
  apply Rle_lt_trans with (a - a'); try psatzl Rdefinitions.R.
  rewrite <- (Rabs_right (a - a')); try psatzl Rdefinitions.R.
  now change (ball a' delta1 a); apply ball_sym; tauto.
exists (fun p => RInt f (fst p) (snd p)); split; cycle 1.
  intros P [eps Peps].
  assert (pre_ep2 : 0 < eps / 2 * /M) by lt0.
  set (ep2 := mkposreal _ pre_ep2).
  destruct (vfi (ball v (pos_div_2 eps))) as [Q R FQ FR vfi'].
    now apply locally_ball.
  exists (eq a) (fun y => R y /\ R2 y).
      exact: ball_eq.
    now apply filter_and.
  intros x y ax [Ry R2y]; simpl; rewrite <- ax; clear ax x.
  apply Peps.
  assert (atrd2 : at_right a (ball a delta2)) by (exists delta2; tauto).
  assert (atre2 : at_right a (ball a ep2)) by (exists ep2; tauto).
  destruct (filter_ex _ (filter_and _ _ atrd1 (filter_and _ _ atrd2
                          (filter_and _ _ FQ (filter_and _ _ FQ2 atre2))))) as
      [a' Pa'].
  replace (pos eps) with (eps/2 + M * (eps / 2 * / M)) by (field; lt0).
  apply ball_triangle with (RInt f a' y).
    replace (RInt f a' y) with (fi (a', y)).
      now apply vfi'; tauto.
    now symmetry; apply is_RInt_unique, ifi; tauto.
  assert (ex_RInt f a a') by (apply exrint_close; tauto).
  change (Rabs (RInt f a y - RInt f a' y) < M * (eps / 2 * / M)).
  apply Rle_lt_trans with (RInt (fun x => Rabs (f x)) (Rmin a a') (Rmax a a')).
  replace (RInt f a y - RInt f a' y) with (RInt f a a'); cycle 1.
    apply Rplus_eq_reg_r with (RInt f a' y).
    now rewrite RInt_Chasles;[ring | | eapply ex_intro; apply ifi]; tauto.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right; try psatzl Rdefinitions.R.
    apply abs_RInt_le; assumption.
  rewrite <- RInt_swap, Rabs_Ropp, Rmin_right, Rmax_left;
        try psatzl Rdefinitions.R.
  apply abs_RInt_le; try psatzl Rdefinitions.R.
  apply ex_RInt_swap; assumption.
  apply Rle_lt_trans with (RInt (fun _ => M) (Rmin a a') (Rmax a a')).
  apply RInt_le.
          now apply Rminmax.
        apply: ex_RInt_continuous.
        rewrite -> Rmin_left, Rmax_right; try apply Rminmax.
        intros z pz; apply continuous_comp;[ | now apply continuous_Rabs].
        apply pd1, Rle_lt_trans with (Rabs (a' - a));[ | tauto].
        unfold abs, minus, plus, opp; simpl.
        destruct (Rle_dec a a') as [aa' | a'a].
          now rewrite -> Rmin_left, Rmax_right in pz; try rewrite !Rabs_right;
          psatzl Rdefinitions.R.
        rewrite -> Rmin_right, Rmax_left in pz; try rewrite (Rabs_left (a' - a));
          try psatzl Rdefinitions.R.
        destruct (Req_dec z a) as [za | nza].
          rewrite -> za,Rplus_opp_r, Rabs_R0; psatzl Rdefinitions.R.
        now rewrite Rabs_left; psatzl Rdefinitions.R.
      now apply ex_RInt_const.
    intros z pz; apply Rlt_le, close.
      destruct (Rle_dec a a') as [aa' | a'a].
        now rewrite -> Rmin_left, Rmax_right in pz; psatzl Rdefinitions.R.
      now rewrite -> Rmin_right, Rmax_left in pz; psatzl Rdefinitions.R.
    apply Rlt_trans with (Rabs (a' - a));[ | tauto].
    unfold abs, minus, plus, opp; simpl.
    destruct (Rle_dec a a') as [aa' | a'a].
      now rewrite -> Rmin_left, Rmax_right in pz; try rewrite !Rabs_right;
          psatzl Rdefinitions.R.
    rewrite -> Rmin_right, Rmax_left in pz; try rewrite (Rabs_left (a' - a));
          try psatzl Rdefinitions.R.
    destruct (Req_dec z a) as [za | nza].
      now rewrite -> za,Rplus_opp_r, Rabs_R0; psatzl Rdefinitions.R.
    now rewrite Rabs_left; psatzl Rdefinitions.R.
  rewrite -> RInt_const, Rmult_comm.
  apply Rmult_lt_compat_l;[psatzl Rdefinitions.R | ].
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmax_right, Rmin_left; try psatzl Rdefinitions.R.
    rewrite <- (Rabs_right (a' - a));[tauto | psatzl Rdefinitions.R].
  rewrite -> Rmax_left, Rmin_right; try psatzl Rdefinitions.R.
  replace (a - a') with (- (a' - a)) by ring.
  now rewrite <- (Rabs_left (a' - a)); try psatzl Rdefinitions.R; tauto.
exists (eq a) R2;[intros z pz; apply ball_eq; exact pz | assumption | ].
intros x y ax qy; rewrite <- ax; clear ax x.
apply RInt_correct; simpl.
destruct (filter_ex _ (filter_and _ _ atrd1 FQ2)) as [a' pa'].
apply ex_RInt_Chasles with a'.
  now apply exrint_close; tauto.
eapply ex_intro; apply ifi; tauto.
Qed.

Lemma inv_sqrt x : 0 < x -> / sqrt x = sqrt (/ x).
Proof.
intros x0.
assert (sqrt x <> 0) by (apply Rgt_not_eq; lt0).
apply Rmult_eq_reg_r with (sqrt x); auto.
rewrite Rinv_l; auto.
rewrite <- sqrt_mult_alt; try lt0.
rewrite -> Rinv_l, sqrt_1; auto with real.
Qed.

Lemma elliptic_agm_step a b c d v : 0 < a -> 0 < b ->
  c = (a + b)/2 -> d = sqrt(a * b) ->
  is_RInt_gen (fun x => /sqrt((x ^ 2 + c ^ 2) * (x ^ 2 + d ^ 2)))
      (Rbar_locally m_infty) (Rbar_locally p_infty) v ->
  is_RInt_gen (fun x => /sqrt((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))
      (Rbar_locally m_infty) (Rbar_locally p_infty) v.
Proof.
intros a0 b0 ceq deq vp.
assert (c0 : 0 < c) by psatzl R.
assert (d0 : 0 < d) by (rewrite deq; lt0).
destruct (ex_un_ell a b) as [w [wp wq]]; auto.
assert (xi := ex_intro _ w wp : ex_RInt_gen _ _ _).
assert (oinfty : filter_Rlt (Rbar_locally m_infty) (Rbar_locally p_infty)).
  now apply (filter_Rlt_witness 0); exists 0; intros; psatzl R.
assert (minfty0 : filter_Rlt (Rbar_locally m_infty) (at_point 0)).
  apply (filter_Rlt_witness (-1));[exists (-1); intros; psatzl R | ].
  now intros y b_y; replace y with 0;[psatzl R | apply ball_eq].
assert (pinfty0 : filter_Rlt (at_point 0) (Rbar_locally p_infty)).
  apply (filter_Rlt_witness 1);[|exists 1; intros; psatzl R].
  now intros x b_x; replace x with 0;[psatzl R | apply ball_eq].
destruct (ex_RInt_gen_cut 0 _ _ _ oinfty minfty0 pinfty0 xi) as [w2 w2p].
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
unfold ell; generalize (iota_correct _ (ex_un_ell a b a0 b0)).
set (ellab := iota _); intros vab.
generalize (iota_correct _ (ex_un_ell _ _ ar0 ge0)).
set (ellab1 := iota _); intros v1.
destruct (ex_un_ell a b a0 b0) as [ww [_ Pww]].
rewrite <- (Pww _ vab).
destruct (ex_un_ell _ _ ar0 ge0) as [ww' [_ Pww']].
now apply (elliptic_agm_step a b) in v1; auto.
Qed.

Lemma quarter_elliptic x : 0 < x -> ell 1 x = 4 * RInt (ellf 1 x) 0 (sqrt x).
Proof.
intros x0.
(* destruct (ex_un_ell 1 x) as [v1 [Pv1 qv1]]; try lt0. *)
assert (m0 : filter_Rlt (Rbar_locally m_infty) (at_point 0)).
  exists (-1), (Rgt (-1)) (Rlt (-1)).
      now exists (-1); intros; psatzl R.
    now intros y bay; replace y with 0;[psatzl R | apply ball_eq ].
  now simpl; intros; psatzl R.
assert (p0 : filter_Rlt (at_point 0) (Rbar_locally p_infty)).
  exists 1, (Rgt 1) (Rlt 1).
      now intros y bay; replace y with 0;[psatzl R | apply ball_eq ].
    now exists 1; intros; psatzl R.
  now simpl; intros; psatzl R.
unfold ell.
generalize (iota_correct _ (ex_un_ell _ _ Rlt_0_1 x0)).
set (v := iota _); intros Pv.
destruct (ex_RInt_gen_cut 0 _ _
          (ellf 1 x) filter_Rlt_m_infty_p_infty
          m0 p0 (ex_intro _ _ Pv)) as [v2 Pv2]; simpl in v, v2.
assert (0 < sqrt x) by lt0.
assert (m0x : filter_Rlt (at_point 0) (at_point (sqrt x))).
  exists (sqrt x / 2), (Rgt (sqrt x / 2)) (Rlt (sqrt x / 2)).
      now intros y bay; replace y with 0;[lt0 | apply ball_eq ].
    now intros y bay; replace y with (sqrt x);[psatzl R | apply ball_eq ].
  now simpl; intros; psatzl R.
assert (mxp : filter_Rlt (at_point (sqrt x)) (Rbar_locally p_infty)).
  exists (2 * sqrt x), (Rgt (2 * sqrt x)) (Rlt (2 * sqrt x)).
      now intros y bay; replace y with (sqrt x);[lt0 | apply ball_eq ].
    now exists (2 * sqrt x); intros; psatzl R.
  now simpl; intros; psatzl R.
destruct (ex_RInt_gen_cut (sqrt x) (at_point 0) _ (ellf 1 x) p0 m0x mxp
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
      now intros y py; apply ball_eq.
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
        now intros y bay; apply ball_eq.
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
    intros P Pp y bay; unfold filtermap; apply Pp.
    assert (qy : sqrt x = y) by now apply ball_eq.
    rewrite <- qy; replace (x / sqrt x) with (sqrt x).
      now intros eps; apply ball_center.
    now rewrite <- (sqrt_sqrt x) at 2; try field; lt0.
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

Local Lemma derive_atan_div_b b t : 0 < b ->
  is_derive (fun x => atan (x / b)) t (b / (b ^ 2 + t ^ 2)).
Proof.
intros b0; auto_derive; auto; field; rewrite Rplus_comm; split; lt0.
Qed.

Lemma is_RInt_gen_equiv F G F' G' (f : R -> R) v:
  (forall s, F s <-> F' s) -> (forall s, G s <-> G' s) ->
  is_RInt_gen f F G v -> is_RInt_gen f F' G' v.
Proof.
intros eqF eqG [inf [[A B FA GB isinf] liminf]].
exists inf; split;[now exists A B; rewrite <- ?eqG, <- ?eqF; auto|].
apply filterlim_filter_le_1 with (2 := liminf).
apply filter_prod_le; intros P;[apply eqF | apply eqG].
Qed.

Lemma ell_lower_bound a b : 0 < a -> 0 < b ->
  PI / Rmax a b <= ell a b.
Proof.
assert (p0 : 0 < PI) by exact PI_RGT_0.
intros a0 b0.
assert (m0 : 0 < Rmax a b) by (apply (Rlt_le_trans _ _ _ a0), Rmax_l).
replace (PI / Rmax a b) with (ell (Rmax a b) (Rmax a b)).
  unfold ell.
  generalize (iota_correct _ (ex_un_ell _ _ m0 m0)).
  set (elm := iota _); intros iselm.
  generalize (iota_correct _ (ex_un_ell _ _ a0 b0)).
  set (ela := iota _); intros isela.
  apply (is_RInt_gen_Rle (ellf a b) _ (ellf (Rmax a b) (Rmax a b)) _
          (Rbar_locally m_infty) (Rbar_locally p_infty)); auto.
      now apply filter_Rlt_m_infty_p_infty.
  apply filter_forall; intros p x _; clear p.
  apply Rle_Rinv; try lt0.
  apply sqrt_le_1_alt; try lt0.
  apply Rmult_le_compat; try lt0.
    now apply Rplus_le_compat_l, pow_incr; split;[lt0 | apply Rmax_l].
  now apply Rplus_le_compat_l, pow_incr; split;[lt0 | apply Rmax_r].
unfold ell.
generalize (iota_correct _ (ex_un_ell _ _ m0 m0)).
set (elm := iota _); intros iselm.
assert (fact1 :
      is_RInt_gen (fun x => / Rmax a b * (/ Rmax a b * /((x / Rmax a b) ^ 2 + 1)))
             (Rbar_locally m_infty)
             (Rbar_locally p_infty) elm).
apply (is_RInt_gen_ext (ellf (Rmax a b) (Rmax a b))); auto.
  apply filter_forall; intros p x _; clear p.
  unfold ellf; rewrite sqrt_square; field_simplify; auto.
      split; lt0.
    lt0.
  unfold Rdiv at 1; rewrite Rmult_0_l; lt0.
assert (fact2 : is_RInt_gen (fun x =>
                       /Rmax a b * (/Rmax a b * /((x /Rmax a b ) ^ 2 + 1)))
            (Rbar_locally m_infty) (Rbar_locally p_infty) (/Rmax a b * PI)).
  now apply/is_RInt_gen_scal/integral_atan_comp_scal.
unfold Rdiv; rewrite Rmult_comm.
case (ex_RInt_gen_unique _ _ _ (ex_intro _ elm fact1)) as [w [isw qw]].
now rewrite <- (qw _ fact2), <- (qw _ fact1); reflexivity.
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
unfold ell.
generalize (iota_correct _ (ex_un_ell _ _ m0 m0)).
set (elm := iota _); intros iselm.
assert (fact1 :
      is_RInt_gen (fun x => / Rmin a b * (/ Rmin a b * /((x / Rmin a b) ^ 2 + 1)))
             (Rbar_locally m_infty)
             (Rbar_locally p_infty) elm).
apply (is_RInt_gen_ext (ellf (Rmin a b) (Rmin a b))); auto.
  apply filter_forall; intros p x _; clear p.
  unfold ellf; rewrite sqrt_square; field_simplify; auto.
      split; lt0.
    lt0.
  unfold Rdiv at 1; rewrite Rmult_0_l; lt0.
assert (fact2 : is_RInt_gen (fun x =>
                       /Rmin a b * (/Rmin a b * /((x /Rmin a b ) ^ 2 + 1)))
            (Rbar_locally m_infty) (Rbar_locally p_infty) (/Rmin a b * PI)).
  now apply/is_RInt_gen_scal/integral_atan_comp_scal.
unfold Rdiv; rewrite Rmult_comm.
case (ex_RInt_gen_unique _ _ _ (ex_intro _ elm fact1)) as [w [isw qw]].
now rewrite <- (qw _ fact2), <- (qw _ fact1); reflexivity.
Qed.

Lemma ag_shift n m a b : ag a b (n + m) = ag (fst (ag a b m)) (snd (ag a b m)) n.
Proof.
revert n a b; induction m.
  now intros; rewrite Nat.add_0_r.
now intros n a b; rewrite Nat.add_succ_r; simpl; apply IHm.
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

Lemma elliptic_to_sin_cos_form a b :
  0 < a -> 0 < b ->
  is_RInt_gen (ellf a b) (Rbar_locally m_infty) (Rbar_locally p_infty)
    (RInt (fun x => /sqrt (a ^ 2 * cos x ^ 2 + b ^ 2 * sin x ^ 2))
      (- PI / 2) (PI / 2)).
Proof.
assert (p0 := PI_RGT_0).
assert (p2q : - (PI / 2) = - PI / 2) by field.
intros a0 b0; set u := (RInt _ _ _).
apply (is_RInt_gen_ext
        (fun t => (b / (b ^ 2 + t ^ 2)) *
                  /sqrt (a ^ 2 * cos (atan (t / b)) ^ 2 +
                         b ^ 2 * sin (atan (t / b)) ^ 2))).
  exists (Rgt 0) (Rlt 0).
      now exists 0; tauto.
    now exists 0; tauto.
  intros x y _ _ z _.
  rewrite (Rplus_comm (b ^ 2)).
  assert (c0 : cos (atan (z / b)) <> 0).
    now apply Rgt_not_eq, cos_gt_0; destruct (atan_bound (z / b)); rewrite ?p2q.
  assert (cq : cos (atan (z / b)) ^ 2 = /((z / b) ^ 2 + 1)).
    rewrite <- (atan_right_inv (z / b)) at 2.
    replace (tan (atan (z / b)) ^ 2 + 1) with
            ((sin (atan (z / b)) ^ 2 + cos (atan (z / b)) ^ 2) /
                  cos (atan (z / b)) ^ 2).
      replace (sin (atan (z / b)) ^ 2 + cos (atan (z / b)) ^ 2) with
        (Rsqr (sin (atan (z / b))) +
            Rsqr (cos (atan (z / b)))) by (unfold Rsqr; ring).
      now rewrite sin2_cos2; field; auto.
    now unfold tan; field; auto.
  assert (sq : sin (atan (z / b)) ^ 2 = 1 - cos (atan (z / b)) ^ 2).
    now simpl; rewrite !Rmult_1_r; apply sin2.
  replace (b / (z ^ 2 + b ^ 2)) with (/ ((z ^ 2 + b ^ 2) / b)); cycle 1.
    field; split; lt0.
  rewrite <- Rinv_mult_distr; try lt0.
  rewrite <- (sqrt_pow2 (_ / b)), <- sqrt_mult_alt; try lt0.
  now unfold ellf; apply f_equal, f_equal; rewrite -> sq, cq; field; split; lt0.
apply (is_RInt_gen_comp (fun x => / sqrt(a ^ 2 * cos x ^ 2 + b ^ 2 * sin x ^ 2))
         (fun t => b / (b ^ 2 + t ^ 2)) (fun t => atan (t / b))).
  exists (Rgt 0) (Rlt 0); try now exists 0; tauto.
  intros x y _ _ z _; split.
    apply: ex_derive_continuous; auto_derive; split; try lt0.
    now split; lt0.
  split;[apply derive_atan_div_b; auto | ].
  now apply: ex_derive_continuous; auto_derive; auto; rewrite Rplus_comm; lt0.
change (Rbar_locally m_infty) with (Rbar_locally' m_infty).
change (Rbar_locally p_infty) with (Rbar_locally' p_infty).
assert (comp_m : Rbar_mult m_infty (/b) = m_infty).
  now apply is_Rbar_mult_unique, is_Rbar_mult_m_infty_pos; simpl; lt0.
assert (comp_p : Rbar_mult p_infty (/b) = p_infty).
  now apply is_Rbar_mult_unique, is_Rbar_mult_p_infty_pos; simpl; lt0.
apply: (is_RInt_gen_filter_le (at_right (-PI/2)) (at_left (PI/2))).
    apply filterlim_comp with (Rbar_locally m_infty).
      evar_last.
        now apply/(is_lim_scal_r (fun x => x) (/b))/is_lim_id.
      now apply f_equal.
    now apply lim_atan_m_infty.
  apply filterlim_comp with (Rbar_locally p_infty).
    evar_last.
      now apply/(is_lim_scal_r (fun x => x) (/b))/is_lim_id.
    now apply f_equal.
  now apply lim_atan_p_infty.
apply: is_RInt_gen_at_point_at_right.
    apply filter_forall; intros x; apply: ex_derive_continuous.
    now auto_derive; repeat split; lt0.
  apply (is_RInt_gen_ext
           (fun x => - ((- 1) * (/ sqrt (a ^ 2 * cos (- x) ^ 2 +
                            b ^ 2 * sin (- x) ^ 2))))).
    apply filter_forall; intros [x y] z _.
    rewrite -> cos_neg, sin_neg; replace ((- sin z) ^ 2) with (sin z ^ 2) by ring.
    (* bug? why ring does not work here? *)
    now rewrite <- Ropp_mult_distr_l, Rmult_1_l, Ropp_involutive; reflexivity.
  rewrite <- (Ropp_involutive u).
  apply: is_RInt_gen_swap.
  apply: (is_RInt_gen_filter_le (filtermap Ropp (at_right (- PI / 2)))
               (filtermap Ropp (at_point (PI / 2)))); cycle 2.
      apply: (is_RInt_gen_comp_opp
                 (fun z => - 1 * /sqrt (a ^ 2 * cos z ^ 2 + b ^ 2 * sin z ^ 2))).
      change (filtermap opp (filtermap Ropp (at_right (-PI /2)))) with
       (filtermap (fun x => Ropp (Ropp x)) (at_right (-PI/2))).
      change (filtermap opp (filtermap Ropp (at_point (PI /2)))) with
       (filtermap (fun x => Ropp (Ropp x)) (at_point (PI/2))).
      apply (is_RInt_gen_equiv  (at_right (-PI / 2)) (at_point (PI/2)));
          try (intros s; unfold filtermap;
               now split; intros C; apply: (filter_imp _ _ _ C);
                    intro; rewrite Ropp_involutive).
      apply: is_RInt_gen_at_point_at_right.
          apply filter_forall; intros x.
          now apply: ex_derive_continuous; auto_derive; repeat split; lt0.
        replace (- u) with ((-1) * u) by ring.
        apply: is_RInt_gen_scal.
        apply/is_RInt_gen_at_point/RInt_correct/ex_RInt_continuous.
        intros x _; assert (tmp := sin_cos_form_pos a b x a0 b0).
        now apply: ex_derive_continuous; auto_derive; repeat split; lt0.
      exists 0, (eq (- PI / 2)) (eq (PI / 2));
          try (intros z bz; apply ball_eq, bz).
      now intros; simpl; psatzl R.
    intros P [eps Peps]; exists eps; intros y B yp; rewrite <- Ropp_involutive.
    apply Peps; try psatzl R; change (Rabs (- y - (- PI / 2)) < eps).
    rewrite -p2q; unfold Rminus; rewrite -> Ropp_involutive, Rplus_comm.
    now apply ball_sym in B; exact B.
  rewrite -p2q; unfold filtermap; intros P PP x B; rewrite <- Ropp_involutive.
  apply PP; intros eps; change (Rabs (-x - (PI/2)) < eps).
  now unfold Rminus; rewrite Rplus_comm; apply (ball_sym (-(PI / 2)) x), B.
exists 0, (eq (- PI / 2)) (Rlt 0); try (intros z bz; apply ball_eq, bz).
  exists (pos_div_2 (mkposreal PI p0)).
  intros y; change (Rabs (y - PI/2) < PI/2 -> y < PI/2 -> 0 < y).
  now intros B yp; revert B; rewrite Rabs_left; psatzl R.
simpl; intros; psatzl R.
Qed.

Lemma isd2 : forall a y t, 0 < a -> 0 < y ->
   is_derive (fun u : R => / sqrt (a ^ 2 * cos t ^ 2 + u ^ 2 * sin t ^ 2)) y
     (- / (a ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2) *
      (/ (2 * sqrt (a ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2)) *
       (2 * y * sin t ^ 2))).
Proof.
intros a y t a0 y0.
auto_derive;[split;[ | split;[ | exact I]]|]; try lt0.
simpl; rewrite -> Rmult_1_r, sqrt_sqrt; ring_simplify; lt0.
Qed.

Definition I_t a b :=
  RInt (fun x => /sqrt(a ^ 2 * cos x ^ 2 + b ^ 2 * sin x ^ 2)) (-PI/2) (PI/2).

Local Lemma half_ball a x (a0 : 0 < a):
  ball a (pos_div_2 (mkposreal _ a0)) x -> 0 < x.
Proof.
intros bax; change (Rabs (x - a) < a/2) in bax.
destruct (Rle_dec 0 (x - a)).
  rewrite Rabs_right in bax; psatzl R.
rewrite Rabs_left in bax; psatzl R.
Qed.

Lemma is_derive_I_t_2 : (* old name q2_1_2_bis_a *)
  forall a b, 0 < a -> 0 < b -> is_derive (fun x => I_t a x) b
     (RInt
      (fun t : R =>
       Derive (fun u : R => / sqrt (a ^ 2 * cos t ^ 2 + u ^ 2 * sin t ^ 2)) b)
       (-PI/2) (PI/2)).
Proof.
intros a b a0 b0.
assert (locally b
          (fun y => ex_RInt
            (fun t => / sqrt (a ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2))
            (- PI / 2) (PI / 2))).
  exists (pos_div_2 (mkposreal _ b0)).
  simpl; intros x xp.
  assert (0 < x) by now apply half_ball in xp.
  apply: ex_RInt_continuous; intros z zc.
  now apply: ex_derive_continuous; auto_derive; repeat split; lt0.
apply is_derive_RInt_param; auto.
  exists (pos_div_2 (mkposreal _ b0)).
  simpl; intros x xp t _.
  assert (0 < x) by now apply half_ball in xp.
  now auto_derive; repeat split; lt0.
intros t _.
apply (continuity_2d_pt_ext_loc
     (fun y t => (- / (a ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2) *
      (/ (2 * sqrt (a ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2)) *
       (2 * y * sin t ^ 2))))); cycle 1.
  assert (sin_cos_form_c2d :
           continuity_2d_pt (fun u v => a ^ 2 * cos v ^ 2 + u ^ 2 * sin v ^ 2)
             b t).
    apply continuity_2d_pt_plus.
      apply (continuity_1d_2d_pt_comp (fun x => a ^ 2 * cos x ^ 2));[reg |].
      now apply continuity_2d_pt_id2.
    apply continuity_2d_pt_mult.
      apply (continuity_1d_2d_pt_comp (fun x => x ^ 2));[reg | ].
      now apply continuity_2d_pt_id1.
    apply (continuity_1d_2d_pt_comp (fun x => sin x ^ 2));[reg | ].
    now apply continuity_2d_pt_id2.
  apply continuity_2d_pt_mult.
    apply (continuity_1d_2d_pt_comp (fun x => - / x)); auto.
    now reg; lt0.
  apply continuity_2d_pt_mult.
    apply (continuity_1d_2d_pt_comp (fun x => / (2 * sqrt x))); auto.
    now reg;[lt0 | lt0 ].
  apply continuity_2d_pt_mult.
    apply (continuity_1d_2d_pt_comp (fun x => 2 * x)); [reg | ].
    now apply continuity_2d_pt_id1.
  apply (continuity_1d_2d_pt_comp (fun x => sin x ^ 2)); [reg | ].
  now apply continuity_2d_pt_id2.
exists (pos_div_2 (mkposreal _ b0)).
intros u v uc vc; symmetry.
now apply is_derive_unique, isd2;[|apply half_ball in uc].
Qed.

Lemma I_deriv_b_neg b: 0 < b -> Derive (fun y => I_t 1 y) b < 0.
Proof.
assert (pi_0 := PI_RGT_0).
assert (vs2 : / 2 = (/ sqrt 2) ^ 2).
  rewrite <- Rinv_pow; try lt0.
  now rewrite sqrt_pow_2; lt0.
intros b0.
assert (pd : forall x t, 0 < x ->
         is_derive (fun y => /sqrt (1 ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2))
          x  ((fun x t => - (x * sin t ^ 2 /
              (sqrt (cos t ^ 2 + x ^ 2 * sin t ^ 2) ^ 3))) x t)).
  intros x t x0; auto_derive; cycle 1.
    replace (1 * (1 * 1) *
       (cos t * (cos t * 1)) + (x * (x * 1) * (sin t * (sin t * 1))))
    with (cos t ^ 2 + x ^ 2 * sin t ^ 2) by ring.
    field; apply Rgt_not_eq, sqrt_lt_R0.
    now replace (cos t ^ 2) with (1 ^ 2 * cos t ^ 2) by ring; lt0.
  now repeat split; lt0.
assert (exists bnd1, (forall t, PI / 4 < t < PI / 2 ->
          Derive (fun y => /sqrt(1 ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2)) b
          <= bnd1) /\ bnd1 < 0) as [bnd1 [Pbnd1 bnd1neg]].
  exists (- (b / 2 * / sqrt (1 + b ^ 2) ^ 3)).
  split; cycle 1.
    now rewrite <- Ropp_0; apply Ropp_lt_contravar; lt0.
  intros t intt.
  rewrite (is_derive_unique _ _ _ (pd b t b0)).
  assert (0 <= sin t - 1 / sqrt 2).
    rewrite <- sin_PI4.
    destruct (MVT_gen sin (PI/4) t cos) as [c [pc1 pc2]];
      try rewrite ->Rmin_left, Rmax_right; try lt0.
        now intros; auto_derive; auto; ring.
      now intros; reg.
    rewrite pc2.
    rewrite -> Rmin_left, Rmax_right in pc1; try lt0.
    assert (0 < cos c) by now apply cos_gt_0; lt0.
    now lt0.
  apply Ropp_le_contravar; unfold Rdiv; apply Rmult_le_compat; try lt0.
    apply Rmult_le_compat_l; try lt0.
    now rewrite vs2; apply pow_incr; split; lt0.
  replace (cos t ^ 2) with (1 ^ 2 * cos t ^ 2) by ring; try lt0.
  apply Rle_Rinv; try lt0.
  apply pow_incr; split; try lt0.
  apply sqrt_le_1; try lt0.
    apply Rplus_le_compat.
    replace (1 ^ 2 * cos t ^ 2) with (cos t ^ 2) by ring.
    replace 1 with (1 ^ 2) by ring.
    destruct (COS_bound t).
    assert (0 < cos t) by now apply cos_gt_0; lt0.
    now apply pow_incr; split; lt0.
  replace (b ^ 2) with (b ^ 2 * 1 ^ 2) at 2 by ring.
  apply Rmult_le_compat_l;[apply pow2_ge_0 | apply pow_incr].
  destruct (SIN_bound t).
  now assert (0 < sin t) by (apply sin_gt_0; lt0); lt0.
rewrite (is_derive_unique _ _ _ (is_derive_I_t_2 1 b Rlt_0_1 b0)).
assert (Pbnd2 : forall t, -PI/2 < t <= PI/ 4 ->
        Derive (fun y => /sqrt(1 ^ 2 * cos t ^ 2 + y ^ 2 * sin t ^ 2)) b <= 0).
intros t _; rewrite (is_derive_unique _ _ _ (pd b t b0)).
  rewrite <- Ropp_0; apply Ropp_le_contravar; unfold Rdiv.
  apply Rmult_le_pos;[apply Rmult_le_pos;[lt0 | apply pow2_ge_0] | ].
  now replace (cos t ^ 2) with (1 ^ 2 * cos t ^ 2) by ring; lt0.
assert (ctd : forall x t, 0 < x -> continuous (fun t => - (x * sin t ^ 2 /
              (sqrt (cos t ^ 2 + x ^ 2 * sin t ^ 2) ^ 3))) t).
  intros x t x0; apply: ex_derive_continuous.
  auto_derive; replace (cos t * (cos t * 1)) with (1 ^ 2 * cos t ^ 2) by ring;
  replace (x * (x * 1) * (sin t * (sin t * 1)))
    with (x ^ 2 * sin t ^ 2) by ring.
  now repeat split; try lt0.
assert (ex_RInt (fun t : R =>
      Derive (fun u : R => / sqrt (1 ^ 2 * cos t ^ 2 + u ^ 2 * sin t ^ 2))
        b) (-PI/2) (PI/4)).
  apply (ex_RInt_ext ((fun x t => - (x * sin t ^ 2 /
              (sqrt (cos t ^ 2 + x ^ 2 * sin t ^ 2) ^ 3))) b)).
    now intros; symmetry; apply is_derive_unique; auto.
  now apply: ex_RInt_continuous; intros z _; apply ctd; lt0.
assert (ex_RInt (fun t : R =>
      Derive (fun u : R => / sqrt (1 ^ 2 * cos t ^ 2 + u ^ 2 * sin t ^ 2))
        b) (PI/4) (PI/2)).
  apply (ex_RInt_ext ((fun x t => - (x * sin t ^ 2 /
              (sqrt (cos t ^ 2 + x ^ 2 * sin t ^ 2) ^ 3))) b)).
    now intros; symmetry; apply is_derive_unique; auto.
  now apply: ex_RInt_continuous; intros z _; apply ctd; lt0.
rewrite <- (RInt_Chasles _ (-PI/2) (PI/4) (PI/2)); auto.
match goal with |- ?x + ?y < 0 => assert (x <= 0 /\ y < 0); try lt0 end.
split.
  replace 0 with (RInt (fun _ => 0) (-PI/2) (PI/4)); cycle 1.
    now rewrite -> RInt_const, Rmult_0_r.
  apply RInt_le; try lt0.
    now apply ex_RInt_const.
  now intros x px; apply Pbnd2; lt0.
apply Rle_lt_trans with ((PI / 2 - PI / 4) * bnd1).
  rewrite <- RInt_const; apply RInt_le; try lt0.
  now apply ex_RInt_const.
now rewrite <- (Rmult_0_r (PI / 2 - PI / 4)); apply Rmult_lt_compat_l; lt0.
Qed.

Lemma ell_I_t a b : 0 < a -> 0 < b ->
  ell a b = I_t a b.
Proof.
intros a0 b0.
unfold ell; generalize (iota_correct _ (ex_un_ell a b a0 b0)).
set (el := iota _); intros Pel.
destruct (ex_RInt_gen_unique _ _ _ (ex_intro _ _ Pel)) as [w [pw qw]].
assert (pi := elliptic_to_sin_cos_form a b a0 b0).
rewrite <- (qw _ Pel); apply (qw _ pi).
Qed.
