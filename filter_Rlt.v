(* This file was tested with coq 8.5.1 and coquelicot 2.1.1 *)

Require Import Reals Coquelicot.Coquelicot Fourier.

Definition filter_Rlt F1 F2 :=
  exists m, filter_prod F1 F2 (fun p => fst p < m < snd p).

Lemma filter_Rlt_witness m (F1 F2  : (R -> Prop) -> Prop) :
  F1 (Rgt m) -> F2 (Rlt m) ->  filter_Rlt F1 F2.
Proof.
exists m; split with (Rgt m) (Rlt m); simpl; auto with real.
Qed.

Lemma filter_Rlt_m_infty_p_infty :
  filter_Rlt (Rbar_locally m_infty) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness 0); exists 0; tauto.
Qed.

Lemma filter_Rlt_m_infty_at_left b :
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

Lemma filter_Rlt_at_right_p_infty b :
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

Lemma filter_Rlt_at_point_p_infty b :
  filter_Rlt (at_point b) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness (b + 1)).
  now intros x bx; replace x with b;[fourier | apply ball_eq].
now exists (b + 1); tauto.
Qed.

Lemma filter_Rlt_m_infty_at_point b :
  filter_Rlt (Rbar_locally m_infty) (at_point b).
Proof.
apply (filter_Rlt_witness (b - 1)).
  now exists (b - 1); tauto.
now intros x bx; replace x with b;[fourier | apply ball_eq].
Qed.

Local Lemma compare_half_sum a b (altb : a < b) : a < (a + b) / 2 < b.
Proof.
assert ((a + b) / 2 * 2 = a + b) by field.
split; apply Rmult_lt_reg_r with 2; fourier.
Qed.

Lemma filter_Rlt_at_point a b : a < b ->
  filter_Rlt (at_point a) (at_point b).
Proof.
intros altb; apply filter_Rlt_witness with ((a + b) / 2).
  intros y b_y; replace y with a;[ | now apply ball_eq].
  destruct (compare_half_sum _ _ altb); tauto.
intros y b_y; replace y with b;[ | now apply ball_eq].
destruct (compare_half_sum _ _ altb); tauto.
Qed.

Lemma Rplus_minus_cancel1 : forall a b, a + b - a = b.
Proof. intros; ring. Qed.

Lemma filter_Rlt_locally a b : a < b ->
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

Lemma filter_Rlt_left_right  a b : a <= b ->
  filter_Rlt (at_left a) (at_right b).
intros ab; apply (filter_Rlt_witness a).
  now exists pos_half; intros y _; apply Rgt_lt.
now exists pos_half; intros y _ yb ; apply Rle_lt_trans with b.
Qed.

Lemma filter_Rlt_trans a F G {FF : Filter F} {GG : Filter G} :
  filter_Rlt F (at_point a) ->
  filter_Rlt (at_point a) G -> filter_Rlt F G.
Proof.
intros [m1 Pm1] [m2 Pm2].
apply filter_Rlt_witness with a.
  destruct Pm1 as [P Q FP atQ cnd1].
  assert (qa : Q a) by now apply atQ; intros; apply ball_center.
  apply (filter_imp P); auto.
  intros x px.
  assert (t := cnd1 x a px qa); simpl in t; destruct t; fourier.
destruct Pm2 as [P Q atP GQ cnd2].
assert (pa : P a) by now apply atP; intros; apply ball_center.
apply (filter_imp Q); auto.
intros x qx.
assert (t := cnd2 a x pa qx); simpl in t; destruct t; fourier.
Qed.

Lemma filter_Rlt_right_left a b : a < b ->
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
intros [m mmid] [gl intg] cmp.
assert (F (Rgt m)).
  destruct mmid as [pf pg fpf gpg cmp'].
  apply (filter_imp pf); destruct (filter_ex pg) as [y py]; auto.
  intros x px; destruct (cmp' x y px py) as [it _]; exact it.
assert (G (Rlt m)).
  destruct mmid as [pf pg fpf gpg cmp'].
  apply (filter_imp pg); destruct (filter_ex (F := F) pf) as [x px]; auto.
  intros y py; destruct (cmp' x y px py) as [_ it]; exact it.
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
Qed.

Lemma is_RInt_gen_Rle (g : R -> R) gl (f : R -> R) fl F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  is_RInt_gen g F G gl ->
  is_RInt_gen f F G fl ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> f x <= g x)) ->
    fl <= gl.
Proof.
intros [m mmid] [Ig [isig limg]] [If [isif limf]] cmp.
apply (fun h => @filterlim_le _ (filter_prod F G) _ If Ig fl gl h limf limg).
apply (fun h => filter_imp _ _ h
        (filter_and _ _ mmid (filter_and _ _ isig (filter_and _ _ isif cmp)))).
clear mmid limf limg isig isif cmp; intros [a b]; simpl.
intros [[am mb] [isig [isif cmp]]].
apply (is_RInt_le f g a b); auto.
  now apply Rlt_le; chain_comparisons; auto.
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
      assert (ma : 0 < m - a) by fourier.
      exists (mkposreal _ ma); simpl; intros z; unfold ball; simpl.
      unfold AbsRing_ball, ball, minus, plus, opp, abs; simpl.
      now intros B az; revert B; rewrite Rabs_right; try split; fourier.
    now apply filter_and.
  intros x y xm fq; simpl; apply RInt_correct.
  apply (ex_RInt_Chasles_2 f a).
    destruct (cmp a y pa); try tauto; intuition; fourier.
  exists (inf (a, y)); apply isinf; try tauto.
  now apply FP1; intros; apply ball_center.
intros P2 [eps P2eps].
set (M := Rabs (f a) + 1).
assert (M0 : 0 < eps / M).
  apply Rmult_lt_0_compat;[destruct eps; simpl; tauto | apply Rinv_0_lt_compat].
  now assert (0 <= Rabs (f a)) by apply Rabs_pos; unfold M; fourier.
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a a').
  intros a' baa'.
  apply (ex_RInt_continuous f); intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; cycle 1.
      destruct pz; fourier.
    destruct pz; apply Rle_lt_trans with (a' - a); try fourier.
    rewrite <- (Rabs_right (a' - a)); try fourier.
    tauto.
  change (Rabs (z - a) < delta1).
  destruct (Rle_dec a z) as [az | za].
    apply Rnot_le_lt in a'a.
    rewrite -> Rmin_right, Rmax_left in pz; try (destruct pz; fourier).
    assert (za' : z = a).
      now apply Rle_antisym; (destruct pz; fourier).
    now rewrite -> za', Rminus_eq_0, Rabs_R0; case delta1; tauto.
  apply Rnot_le_lt in a'a; apply Rnot_le_lt in za.
  rewrite -> Rmin_right, Rmax_left in pz; try fourier.
  rewrite Rabs_left;[ | fourier].
  apply Rle_lt_trans with (a - a'); try (intuition fourier).
  rewrite <- (Rabs_right (a - a')); try (intuition fourier).
  now change (ball a' delta1 a); apply ball_sym; tauto.
destruct (limf (ball v (pos_div_2 eps))) as [Ql Rl FQl FRl vfi'].
  now apply locally_ball.
assert (pre_ep2 : 0 < eps / 2 * /M).
  repeat apply Rmult_lt_0_compat; try fourier;[destruct eps; tauto | ].
  now apply Rinv_0_lt_compat; unfold M; assert (t := Rabs_pos (f a)); fourier.
set (ep2 := mkposreal _ pre_ep2).
assert (at_right a (fun x => ball a delta1 x /\ ball a ep2 x /\
                             ball a delta2 x /\ a < x /\ x < m)).
  repeat apply filter_and; try (now apply filter_le_within, locally_ball).
    now exists ep2; intros; tauto.
  destruct (filter_ex _ FQ) as [y' Py'].
  assert (ma0 : 0 < m - a).
    now destruct (cmp a y'); auto; fourier.
  exists (mkposreal _ ma0); simpl; intros y.
  intros bay ay; change (Rabs (y - a) < m - a) in bay.
  now rewrite -> Rabs_right in bay; fourier.
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
      now apply exrint_close; tauto.
    intros t atx.
    replace (f t) with (f a + (f t - f a)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat;[apply Rle_refl | ].
    apply Rlt_le, (Pd2 t).
    change (Rabs (t - a) < delta2); rewrite Rabs_right;[ | intuition fourier].
    apply Rle_lt_trans with (x - a);[intuition fourier | ].
    now rewrite <- (Rabs_right (x - a));[tauto | intuition fourier].
  replace (pos (pos_div_2 eps)) with (ep2 * M).
    rewrite <- (Rabs_right (x - a));[|intuition fourier].
    apply Rmult_lt_compat_r;[unfold M  | tauto].
    now assert (t := Rabs_pos (f a)); fourier.
  simpl; field; unfold M; apply Rgt_not_eq; assert (t := Rabs_pos (f a)).
  now fourier.
apply ball_triangle with (RInt f a y); cycle 1.
  change (Rabs (RInt f x y - RInt f a y) < pos_div_2 eps).
  replace (RInt f a y) with (RInt f a x + RInt f x y); cycle 1.
  apply RInt_Chasles.
      now apply exrint_close; tauto.
    apply (ex_RInt_Chasles_2 f a).
      split;[apply Rlt_le; tauto | apply Rlt_le, Rlt_trans with m; try tauto].
    now destruct (cmp a y); tauto.
  exists (inf (a, y)); apply isinf.
    now apply FP1; intros; apply ball_center.
  now tauto.
  match goal with |- Rabs ?v < _ => replace v with (-RInt f a x) by ring end.
  now rewrite -> Rabs_Ropp.
rewrite (is_RInt_unique f a y (inf(a, y))); cycle 1.
  now apply isinf;[apply FP1; intros; apply ball_center | tauto].
now apply vfi';[apply FQl; intros; apply ball_center | tauto].
Qed.

Lemma ex_RInt_gen_cut (a : R) (F G: (R -> Prop) -> Prop)
   {FF : ProperFilter F} {FG : ProperFilter G} (f : R -> R) :
   filter_Rlt F (at_point a) -> filter_Rlt (at_point a) G ->
   ex_RInt_gen f F G -> ex_RInt_gen f (at_point a) G.
Proof.
intros lFa laG [l [g [ifg vfg]]].
assert (lFG := filter_Rlt_trans _ _ _ lFa laG).
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
     [destruct (lFa x a) | destruct(laG a y)]; (intuition fourier || tauto) | ].
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
    assert (x < a) by (destruct (lFa x a); intuition fourier || tauto).
    assert (a < y) by (destruct (laG a y); intuition fourier || tauto).
    assert (a < z) by (destruct (laG a z); intuition fourier || tauto).
    assert (ex_RInt f x a).
      apply (ex_RInt_Chasles_1 f x a y);[intuition fourier | assumption].
    rewrite !RInt_Chasles; auto;
       try (apply (ex_RInt_Chasles_2 f x); auto; intuition fourier); cycle 1.
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
unfold filtermap in t.
apply (Filter_prod (at_point a) G _ (eq a)
               (fun x =>
                  ball (R_complete_lim (fun P => G (fun y => P (RInt f a y))))
                       eps (RInt f a x))
        (ball_eq _) t).
intros x y <-; tauto.
Qed.

