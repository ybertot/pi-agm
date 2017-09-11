Require Import Reals Coquelicot.Coquelicot Fourier.

Definition filter_Rlt F G :=
  exists m, filter_prod F G (fun p => fst p < m < snd p).

Lemma filter_Rlt_witness m (F G  : (R -> Prop) -> Prop) :
  F (Rgt m) -> G (Rlt m) ->  filter_Rlt F G.
Proof.
exists m; split with (Rgt m) (Rlt m); simpl; auto with real.
Qed.

Lemma filter_Rlt_m_infty_p_infty :
  filter_Rlt (Rbar_locally m_infty) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness 0); exists 0; tauto.
Qed.

Example filter_Rlt_m_infty_at_left b :
  filter_Rlt (Rbar_locally m_infty) (at_left b).
Proof.
apply (filter_Rlt_witness (b - 1)).
  now exists (b - 1); intros x cmpx; apply Rlt_gt.
exists pos_half; intros x yb _.
enough (b - x  < 1) by fourier.
apply Rle_lt_trans with (abs (minus b x)).
  now apply Rle_abs.
apply ball_sym in yb; apply AbsRing_norm_compat2 in yb.
apply Rlt_trans with (1 := yb).
rewrite Rmult_1_l; simpl.
fourier.
Qed.

Example filter_Rlt_at_right_p_infty b :
  filter_Rlt (at_right b) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness (b + 1)).
  exists pos_half; intros y yb _.
  enough (y - b < 1) by fourier.
  apply Rle_lt_trans with (abs (minus y b)).
    now apply Rle_abs.
  apply AbsRing_norm_compat2 in yb.
  apply Rlt_trans with (1 := yb).
  rewrite Rmult_1_l; simpl.
  fourier.
now exists (b + 1); intros x cmpx.
Qed.

Lemma Rplus_minus_cancel1 : forall a b, a + b - a = b.
Proof. intros; ring. Qed.

Example filter_Rlt_locally a b : a < b ->
  filter_Rlt (Rbar_locally a) (Rbar_locally b).
Proof.
intros ab.
assert (bmap: 0 < (b - a)/2).
  apply Rmult_lt_reg_r with 2;[fourier | ].
  unfold Rdiv; rewrite Rmult_0_l, Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r;[ | apply Rgt_not_eq]; fourier.
apply (filter_Rlt_witness ((a + b)/2)).
  exists (mkposreal _ bmap); intros y ya.
  enough (yma : y * 2 - a * 2 < b - a).
    apply Rmult_lt_reg_r with 2;[fourier | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; fourier].
    rewrite Rmult_1_r; fourier.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
    apply Rinv_0_lt_compat; fourier.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; fourier].
  apply Rle_lt_trans with (abs (minus y a)).
    now apply Rle_abs.
  apply AbsRing_norm_compat2 in ya; apply Rlt_le_trans with (1 := ya).
  now rewrite Rmult_1_l; simpl; auto with real.
exists (mkposreal _ bmap); intros y yb.
enough (yma : b * 2 - y * 2 < b - a).
  apply Rmult_lt_reg_r with 2;[fourier | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; fourier].
  rewrite Rmult_1_r; fourier.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
  apply Rinv_0_lt_compat; fourier.
rewrite Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; fourier].
apply Rle_lt_trans with (abs (minus b y)).
  now apply Rle_abs.
apply ball_sym in yb; apply AbsRing_norm_compat2 in yb.
  apply Rlt_le_trans with (1 := yb).
now rewrite Rmult_1_l; simpl; auto with real.
Qed.

Example filter_Rlt_left_right  a b : a <= b ->
  filter_Rlt (at_left a) (at_right b).
intros ab; apply (filter_Rlt_witness a).
  now exists pos_half; intros y _; apply Rgt_lt.
now exists pos_half; intros y _ yb ; apply Rle_lt_trans with b.
Qed.

Example filter_Rlt_right_left a b : a < b ->
  filter_Rlt (at_right a) (at_left b).
Proof.
intros ab.
assert (bmap: 0 < (b - a)/2).
  apply Rmult_lt_reg_r with 2;[fourier | ].
  unfold Rdiv; rewrite Rmult_0_l, Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r;[ | apply Rgt_not_eq]; fourier.
apply (filter_Rlt_witness ((a + b)/2)).
  exists (mkposreal _ bmap); intros y ya cmp.
  enough (yma : y * 2 - a * 2 < b - a).
    apply Rmult_lt_reg_r with 2;[fourier | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; fourier].
    rewrite Rmult_1_r; fourier.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
    apply Rinv_0_lt_compat; fourier.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; fourier].
  apply Rle_lt_trans with (abs (minus y a)).
    now apply Rle_abs.
  apply AbsRing_norm_compat2 in ya; apply Rlt_le_trans with (1 := ya).
  now rewrite Rmult_1_l; simpl; auto with real.
exists (mkposreal _ bmap); intros y yb cmp.
enough (yma : b * 2 - y * 2 < b - a).
  apply Rmult_lt_reg_r with 2;[fourier | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; fourier].
  rewrite Rmult_1_r; fourier.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
  apply Rinv_0_lt_compat; fourier.
rewrite Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; fourier].
apply Rle_lt_trans with (abs (minus b y)).
  now apply Rle_abs.
apply ball_sym in yb; apply AbsRing_norm_compat2 in yb.
  apply Rlt_le_trans with (1 := yb).
now rewrite Rmult_1_l; simpl; auto with real.
Qed.

Local Ltac chain_comparisons :=
  match goal with
  | h : ?a <= _ |- ?a < _ => apply Rle_lt_trans with (1 := h)
  | h : _ <= ?a |- _ < ?a => apply Rlt_le_trans with (2 := h)
  | h : ?a < _ |- ?a < _ => apply Rlt_trans with (1 := h)
  | h : _ < ?a |- _ < ?a => apply Rlt_trans with (2 := h)
  end.

Lemma ex_RInt_gen_bound (g : R -> R) (f : R -> R) F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  ex_RInt_gen g F G ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> 0 <= f x <= g x) /\
       ex_RInt f (fst p) (snd p)) ->
    ex_RInt_gen f F G.
Proof.
Admitted.
(* intros [m mmid] [gl intg] cmp.
assert (F (Rgt m)).
  destruct mmid as [pf pg fpf gpg cmp'].
  apply (filter_imp pf); destruct (filter_ex pg) as [y py]; auto.
  intros x px; destruct (cmp' x y px py) as [it _]; exact it.
assert (G (Rlt m)).
  destruct mmid as [pf pg fpf gpg cmp'].
  apply (filter_imp pg); destruct (filter_ex (F := F) pf) as [x px]; auto.
  intros y py; destruct (cmp' x y px py) as [_ it]; exact it.
(* experimenting here. *)
exists (lim (filtermap (fun p => RInt f (fst p) (snd p)) (filter_prod F G))).
intros P [eps Peps]. exists (Rgt m) (Rlt m); auto.
destruct 
exists (lim (filtermap (fun p => RInt f (fst p) (snd p)) (filter_prod F G))).

unfold is_RInt_gen.
unfold filtermapi.

destruct HP as [A B].
assert (t := intg (ball gl (mkposreal _ Rlt_0_1))).
  unfold filtermapi in t.

destruct intg as [Ig [isig cvi]].
exists (lim (filtermap (fun p => RInt f (fst p) (snd p)) (filter_prod F G))).
destruct cmp as [Q1 R1 fq1 gr1 cmp]; simpl in cmp.
assert (cc : cauchy (filtermap (fun p => RInt f (fst p) (snd p))
                       (filter_prod F G))).
  intros eps; destruct (cvi _ (locally_ball gl (pos_div_2 eps)))
                as [Qs Rs fqs grs main].
  destruct isig as [Q0 R0 fq0 gr0 isig].
  assert (fq : F (fun x => Q0 x /\ Q1 x /\ Qs x /\ m > x))
    by now repeat apply filter_and.
  assert (gr : G (fun y => R0 y /\ R1 y /\ Rs y /\ m < y))
    by now repeat apply filter_and.
  destruct (filter_ex _ fq) as [x qx], (filter_ex _ gr) as [y ry].
  exists (RInt f x y).
  exists (fun x => Q0 x /\ Q1 x /\ Qs x /\ m > x)
         (fun y => R0 y /\ R1 y /\ Rs y /\ m < y);
    try now repeat apply filter_and.
  intros u v Qu Rv.
  assert (wlog_cc : forall a b c d,
            Q0 a /\ Q1 a /\ Qs a ->
            Q0 b /\ Q1 b /\ Qs b ->
            R0 c /\ R1 c /\ Rs c ->
            R0 d /\ R1 d /\ Rs d ->
            a <= b -> c <=d -> b < m -> m < c ->
            (ball (RInt f a d) eps (RInt f b c) /\
            ball (RInt f a c) eps (RInt f b d))).
    clear x y qx ry u v Qu Rv; intros a b c d Qa Qb Rc Rd ab cd bm mc.
    assert (ex_RInt f a c /\ ex_RInt f b c /\ ex_RInt f b d).
      now repeat apply conj; apply cmp.
    assert (ex_RInt g a c /\ ex_RInt g b c /\ ex_RInt g b d).
      now repeat apply conj; eapply ex_intro; eapply isig.
    assert (ex_RInt f a b).
      now apply ex_RInt_Chasles with c;[ | apply ex_RInt_swap].
    assert (ex_RInt f c d).
      now apply ex_RInt_Chasles with b;[apply ex_RInt_swap | ].
    assert (ex_RInt g a b).
      now apply ex_RInt_Chasles with c;[ | apply ex_RInt_swap].
    assert (ex_RInt g c d).
      now apply ex_RInt_Chasles with b;[apply ex_RInt_swap | ].
    assert (bc : b < c) by (apply Rlt_trans with m; tauto).
    split.
      apply ball_sym, Rle_lt_trans with (Rabs (RInt g a d - RInt g b c)).
        rewrite <- (RInt_Chasles f a b d), <- (RInt_Chasles f b c d),
                <- (RInt_Chasles g a b d), <- (RInt_Chasles g b c d),
               !(Rplus_comm (RInt _ a b)), !Rplus_assoc, !Rplus_minus_cancel1;
         try tauto.
        unfold abs; simpl; rewrite !Rabs_right;
        try (apply Rle_ge, Rplus_le_le_0_compat; apply RInt_ge_0; auto);
(* The following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
        apply Rplus_le_compat; apply RInt_le; try tauto;
(* the following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
      change (ball (RInt g b c) eps (RInt g a d)).
      replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
      apply ball_triangle with gl.
        replace (RInt g b c) with (Ig (b,c)).
          apply ball_sym, main; tauto.
        symmetry; apply is_RInt_unique, isig; tauto.
      replace (RInt g a d) with (Ig(a,d)).
        apply main; tauto.
      symmetry; apply is_RInt_unique, isig; tauto.
    change (Rabs (RInt f b d + - RInt f a c) < eps).
    rewrite <- (RInt_Chasles f b c d), <- (RInt_Chasles f a b c),
      Ropp_plus_distr, !Rplus_assoc, (Rplus_comm (RInt f b c)), !Rplus_assoc,
      Rplus_opp_l, Rplus_0_r; try tauto.
    apply Rle_lt_trans with (1 := Rabs_triang _ _);
       rewrite Rabs_Ropp, !Rabs_right;
    try (apply Rle_ge, RInt_ge_0; try tauto);
(* the following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
    replace (pos eps) with (pos_div_2 eps + pos_div_2 eps)
             by (simpl; field).
     assert (dc : RInt f c d <= RInt g c d /\ RInt f a b <= RInt g a b).
      split; apply RInt_le; try tauto;
(* the following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
    apply Rle_lt_trans with (1 := Rplus_le_compat _ _ _ _ (proj1 dc)(proj2 dc)).
    apply Rle_lt_trans with (1 := Rle_abs _).
    replace (RInt _ _ _ + _) with
      ((RInt g a d - gl) - (RInt g b c - gl))
    by (rewrite <- (RInt_Chasles g a b d), <- (RInt_Chasles g b c d); 
            try tauto; ring).
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
      replace (RInt g a d) with (Ig(a, d)).
        apply (main a d); tauto.
      symmetry; apply is_RInt_unique, isig; tauto.
    rewrite Rabs_Ropp; replace (RInt g b c) with (Ig(b,c)).
      apply (main b c); tauto.
    symmetry; apply is_RInt_unique, isig; tauto.
  destruct (Rlt_dec x u), (Rlt_dec v y);
   [apply (wlog_cc x u v y) | apply (wlog_cc x u y v) |
    apply ball_sym, (wlog_cc u x v y) | apply ball_sym, (wlog_cc u x y v)];
    try split;
    try solve[tauto | apply Rlt_le; tauto |
      apply Rge_le; tauto | apply Rle_ge; tauto|
      apply Rnot_lt_le; tauto].
assert (main : forall eps:posreal, filtermap (fun p => RInt f (fst p) (snd p))
              (filter_prod F G)
               (ball (lim (filtermap (fun p => RInt f (fst p) (snd p)) 
                             (filter_prod F G))) eps)).
  intros eps; apply complete_cauchy;
     [apply filtermap_proper_filter;apply filter_prod_proper| exact cc].
exists (fun p =>  RInt f (fst p) (snd p)); split.
  exists Q1 R1; auto.
  now intros x y qx ry; apply RInt_correct, cmp.
intros P [eps Peps]; destruct (main eps) as [Q' R' fQ' gR' B].
  now exists Q' R'; auto.
Qed. *)

Lemma is_RInt_gen_Rle (g : R -> R) gl (f : R -> R) fl F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  is_RInt_gen g F G gl ->
  is_RInt_gen f F G fl ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> f x <= g x)) ->
    fl <= gl.
Proof.
Admitted.
(*
intros [m mmid] [Ig [isig limg]] [If [isif limf]] cmp.
apply (fun h => @filterlim_le _ (filter_prod F G) _ If Ig fl gl h limf limg).
apply (fun h => filter_imp _ _ h
        (filter_and _ _ mmid (filter_and _ _ isig (filter_and _ _ isif cmp)))).
clear mmid limf limg isig isif cmp; intros [a b]; simpl.
intros [[am mb] [isig [isif cmp]]].
apply (is_RInt_le f g a b); auto.
  now apply Rlt_le; chain_comparisons; auto.
Qed. *)

