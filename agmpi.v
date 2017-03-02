Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral.
Require Import elliptic_integral arcsinh generalities.
Require Import Interval.Interval_tactic.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

Definition u_ (n : nat) (x : R) := fst(ag 1 x n).

Definition ff (x : R) := M 1 x.

Definition w_ (n : nat) x :=
  sqrt (fst(ag 1 x n) ^ 2 - snd (ag 1 x n) ^ 2).

Definition k_ n x := / (2 ^ n) * ln (u_ n x / w_ n x).

Lemma M_between a b n : 0 < a -> 0 < b -> b <= a ->
   snd (ag a b n) <= M a b <= fst (ag a b n).
Proof.
intros a0 b0 ba; rewrite <- (M_shift _ _ n); try lt0.
apply Mbounds; auto; destruct (ag_le n _ _ a0 b0); try lt0.
Qed.

Lemma dist_u_ff :
  forall n x, (1 <= n)%nat -> 0 < x -> 0 <= u_ n x - ff x <= Rabs(1 - x)/2^n.
Proof.
intros n x n1 x0; destruct (Rle_dec 0 (1 - x)) as [x1' | x1'].
  assert (x1 : x <= 1) by psatzl R.
  assert (t := agm_conv 1 x n Rlt_0_1 x0 x1).
  rewrite Rabs_right; try lt0.
  now unfold u_, ff; destruct (M_between 1 x n); lt0.
assert (x1 : 1 <= x) by lt0.
assert (t := agm_conv x 1 n x0 Rlt_0_1 x1).
rewrite Rabs_left; try lt0.
unfold u_, ff; rewrite M_swap; try lt0.
rewrite ag_swap; try lia; try lt0.
destruct (M_between x 1 n); try lt0.
Qed.

Lemma cvu_u_ff : forall x (x0 : 0 < x < 1) (d : posreal),
  (d = (1 - x / 2) / 2 :> R) -> CVU u_ ff ((1 + x / 2) / 2) d.
Proof.
intros x x0 d dq eps ep.
destruct (cv_div2 (1 - x / 2) (ball 0 (mkposreal _ ep)) (locally_ball 0 _)) as
  [N pn].
exists (N + 1)%nat; intros n y Nn dyx.
assert (n1 : (1 <= n)%nat) by lia.
unfold Boule in dyx; apply Rabs_lt_between in dyx; unfold pos_div_2;
 simpl in dyx.
assert (y0 : 0 < y) by psatzl R.
destruct  (dist_u_ff n y n1 y0) as [difpos difbound].
rewrite <- Rabs_Ropp, Rabs_pos_eq, Ropp_minus_distr';[ | psatzl R].
apply Rle_lt_trans with (1 := difbound).
assert (Nn' : (n >= N)%nat) by lia.
assert (Pn' := pn n Nn').
apply Rabs_def2 in Pn'; unfold minus, plus, opp in Pn'; simpl in Pn'.
apply Rlt_trans with (2 := proj1 Pn'); rewrite -> Ropp_0, Rplus_0_r.
now apply Rmult_lt_compat_r;[lt0 | apply Rabs_def1; psatzl R].
Qed.

Lemma ex_derive_ag n x : 0 < x ->
  {d1 : R & {d2 | is_derive (fun x => fst (ag 1 x n)) x d1 /\
              is_derive (fun x => snd (ag 1 x n)) x d2 /\
              0 <= d1 /\ 0 < d2 /\ ((1 <= n)%nat -> 0 < d1)}}.
Proof.
intros x0; induction n.
  now exists 0, 1; split;[ | split];[ | | repeat split; try lia; psatzl R];
  simpl; auto_derive; auto.
destruct IHn as [d1 [d2 [dd1 [dd2 [d1_0 [d2_0 d1gt]]]]]].
exists ((d1 + d2) / 2), ((fst (ag 1 x n) * d2 + snd (ag 1 x n) * d1) /
                       (2 * sqrt(fst (ag 1 x n) * snd (ag 1 x n)))).
assert (0 < fst (ag 1 x n) /\ 0 < snd (ag 1 x n)).
  destruct (Rle_dec x 1) as [x1 | x1'].
    now assert (t := ag_le n 1 x Rlt_0_1 x0 x1); psatzl R.
  destruct n as [|p]; [simpl; psatzl R | ].
  now rewrite ag_swap; destruct (ag_le (S p) x 1 x0 Rlt_0_1); try psatzl R; lia.
split.
  apply (is_derive_ext (fun y => /2 * (fst (ag 1 y n) + snd (ag 1 y n)))).
    intros y; replace (S n) with (1 + n)%nat by ring; rewrite ag_shift.
    now simpl; field.
  replace ((d1 + d2) / 2) with (/2 * (d1 + d2)) by field.
  now apply/is_derive_scal/is_derive_plus.
split.
  apply (is_derive_ext (fun y => sqrt (fst (ag 1 y n) * snd (ag 1 y n)))).
    now intros y; replace (S n) with (1 + n)%nat by ring; rewrite ag_shift.
  evar_last.
    apply is_derive_sqrt; try lt0.
    apply: is_derive_mult;[exact dd1 | exact dd2 | exact Rmult_comm].
  unfold plus, mult; simpl.
  now rewrite -> (Rmult_comm d1), (Rplus_comm (_ * d1)).
split;[lt0 | split;[ | now intros _; lt0]].
apply Rmult_lt_0_compat;[ | lt0].
now apply Rplus_lt_le_0_compat;[lt0 | apply Rmult_le_pos]; lt0.
Qed.

Lemma ag_lt n a b : 0 < b < a -> snd (ag a b n) < fst (ag a b n).
Proof.
revert a b; induction n.
  simpl; intros; psatzl R.
simpl; intros a b [b0 a0]; apply IHn; split;[lt0 | ].
destruct (Rlt_dec (sqrt (a * b)) ((a + b) / 2)) as [inf | sup]; auto.
assert (sup' : 0 <= (a + b) / 2 <= sqrt (a * b)) by psatzl R.
apply (pow_incr _ _ 2) in sup'; revert sup'.
rewrite sqrt_pow_2; try lt0; intros sup'; apply Rle_minus in sup'.
set (v := ((a - b) / 2) ^ 2).
match goal with _ : ?x <= 0 |- _ => assert (q: x = v) by (unfold v; field) end.
assert (v = 0) by (apply Rle_antisym; unfold v; lt0).
destruct (Req_dec (b - a) 0) as [abs | abs]; unfold v in *; try psatzl R.
apply pow2_gt_0 in abs; psatzl R.
Qed.

Definition y_ n x := u_ n x / snd (ag 1 x n).

Definition yfun y := (1 + y) / (2 * sqrt y).

Lemma y_step n x : 0 < x < 1 ->
   y_ (n + 1) x = yfun (y_ n x).
Proof.
intros intx; unfold yfun, y_, u_; rewrite -> Nat.add_comm, ag_shift; simpl.
destruct (ag_le n 1 x); try lt0; rewrite -> sqrt_mult, sqrt_div; try lt0.
set (u := sqrt (snd _)); rewrite <- (sqrt_pow_2 (snd _)); try lt0; unfold u.
field; repeat split; lt0.
Qed.

Lemma derive_y_step x : 0 < x ->
  is_derive yfun x ((x - 1) / (4 * sqrt x ^ 3)).
Proof.
intros x0; unfold yfun; evar_last;[now auto_derive; repeat split; lt0 | ].
set (u := sqrt x); rewrite <- (sqrt_sqrt x); fold u; try lt0.
now field; unfold u; lt0.
Qed.

Lemma y_gt_1 : forall x n, 0 < x < 1 -> 1 < y_ n x.
intros x n intx.
unfold y_; replace (u_ n x) with
   (snd (ag 1 x n) + (u_ n x - (snd (ag 1 x n)))) by ring.
unfold Rdiv; rewrite Rmult_plus_distr_r.
assert (t := ag_lt n 1 x intx).
assert (t' := ag_le n 1 x Rlt_0_1 (proj1 intx) (Rlt_le _ _ (proj2 intx))).
  rewrite Rinv_r; [ | psatzl R].
replace 1 with (1 + 0) at 1 by ring; apply Rplus_lt_compat_l; unfold u_; lt0.
Qed.

Lemma yfun_derive y : 1 < y ->
  0 < Derive yfun y.
Proof.
intros cy.
assert (tmp: is_derive yfun y ((y - 1) / (4 * sqrt y ^ 3))).
  unfold yfun; auto_derive.
    now repeat split; lt0.
  field_simplify; try lt0.
  replace ((sqrt y) ^ 2) with y.
    now field_simplify; try lt0; auto.
  now simpl; rewrite -> Rmult_1_r, sqrt_sqrt; lt0.
rewrite (is_derive_unique _ _ _ tmp).
now lt0.
Qed.

Lemma exdy x : 0 < x -> ex_derive yfun x.
Proof.
now intros x0; unfold yfun; auto_derive; repeat split; lt0.
Qed.

Lemma y_decr x y n : 0 < x < 1 -> 0 < y < 1 -> x < y ->
  y_ n y < y_ n x.
Proof.
intros cx cy xy; induction n as [ | n IHn].
  unfold y_, u_; simpl.
  now unfold Rdiv; rewrite !Rmult_1_l; apply Rinv_lt_contravar; lt0.
replace (S n) with (n + 1)%nat by ring; rewrite !y_step; auto.
assert (tmp : 1 < y_ n y) by now apply y_gt_1; psatzl R.
assert (exd' : forall c, y_ n y <= c <= y_ n x->
               derivable_pt_lim yfun c (Derive yfun c)).
  intros c cc; rewrite <- is_derive_Reals.
  now apply Derive_correct, exdy; psatzl R.
destruct (MVT_cor2 yfun (Derive yfun) (y_ n y) (y_ n x) IHn exd') as
 [c [pc cc]].
apply Rplus_lt_reg_r with (- (yfun (y_ n y))).
rewrite Rplus_opp_r; unfold Rminus in pc; rewrite pc.
assert (0 < Derive yfun c).
  now apply yfun_derive; psatzl R.
now lt0.
Qed.

Lemma derive_fst_step n x : 0 < x < 1 ->
  Derive (u_ (S n)) x = (Derive (u_ n) x + Derive (fun x => snd (ag 1 x n)) x)
   / 2.
Proof.
intros intx; rewrite (Derive_ext _ (fun x => /2 * (u_ n x + snd (ag 1 x n)))).
  destruct (ex_derive_ag n x) as [d [e Ps]]; try lt0.
  assert (ex_derive (u_ n) x) by (exists d; tauto).
  assert (ex_derive (fun x => snd (ag 1 x n)) x) by (exists e; tauto).
  evar_last.
    now rewrite -> Derive_scal, Derive_plus; auto.
  now field.
intros; unfold u_; change (S n) with (1 + n)%nat.
now rewrite -> ag_shift, Rmult_comm.
Qed.

Lemma derive_snd_step n x : 0 < x < 1 ->
  Derive (fun y => snd (ag 1 y (S n))) x =
  (Derive (u_ n) x  * snd (ag 1 x n) +
   Derive (fun x => snd (ag 1 x n)) x * fst (ag 1 x n))
   / (2 * sqrt (fst (ag 1 x n)) * sqrt (snd (ag 1 x n))).
Proof.
intros intx.
destruct (ex_derive_ag n x) as [d [e Ps]]; try lt0.
destruct (ag_le n 1 x); try lt0.
rewrite (Derive_ext _ (fun x => sqrt (u_ n x * snd (ag 1 x n)))).
  assert (ex_derive (u_ n) x) by (exists d; tauto).
  assert (ex_derive (fun x => snd (ag 1 x n)) x) by (exists e; tauto).
  evar_last.
    apply is_derive_unique; apply is_derive_sqrt.
      apply: is_derive_mult.
          now apply Derive_correct; exact (ex_intro _ _ (proj1 Ps)).
        now apply Derive_correct; exact (ex_intro _ _ (proj1 (proj2 Ps))).
      now intros; apply Rmult_comm.
    now unfold u_; lt0.
  unfold plus, mult; simpl; rewrite sqrt_mult; try (unfold u_; lt0).
  now unfold u_; field; split; lt0.
intros; unfold u_; change (S n) with (1 + n)%nat.
now rewrite -> ag_shift.
Qed.

Definition z_ n x := Derive (fun x => snd (ag 1 x n)) x / Derive (u_ n) x.

Lemma z_1 x : 0 < x < 1 -> z_ 1 x = / sqrt(x).
Proof.
intros cx; unfold z_.
assert (dv : Derive (fun x => snd (ag 1 x 1)) x = 1 / (2 * sqrt(x))).
  apply is_derive_unique, (is_derive_ext sqrt).
    now intros t; simpl; rewrite Rmult_1_l.
  auto_derive;[tauto | reflexivity].
assert (du : Derive (u_ 1) x = 1 / 2).
  apply is_derive_unique, (is_derive_ext (fun x => (1 + x)/2)); auto.
  auto_derive;[tauto | reflexivity].
rewrite -> dv, du; field; lt0.
Qed.

Lemma z_step n x : (1 <= n)%nat -> 0 < x < 1 ->
  z_ (n + 1) x = (1 + z_ n x * y_ n x) / ((1 + z_ n x) * sqrt (y_ n x)).
Proof.
intros n1 intx; unfold z_, y_.
destruct (ag_le n 1 x); destruct (ex_derive_ag n x) as [d [e P]]; try lt0.
assert (0 < d) by tauto.
replace (n + 1)%nat with (S n) by ring; rewrite derive_fst_step; try lt0.
rewrite derive_snd_step; try lt0.
unfold u_; set (a := fst (ag _ _ _)); set (b := snd (ag _ _ _)).
set (t := sqrt a); set u := sqrt b.
rewrite (is_derive_unique _ _ _ (proj1 P))
       (is_derive_unique _ _ _ (proj1 (proj2 P))).
rewrite sqrt_div; try (unfold a, b; lt0); fold t; fold u.
rewrite <- (sqrt_sqrt a), <- (sqrt_sqrt b); try (unfold a, b; lt0).
now fold t; fold u; field; unfold t, u, a, b; repeat split; lt0.
Qed.

Lemma derive_z_step y x : 0 < x -> 0 < y ->
  is_derive (fun z => (1 + z * y) / ((1 + z) * sqrt y)) x
      ((y - 1) / ((x + 1) ^ 2 * sqrt y)).
Proof.
intros x0 y0; evar_last; [auto_derive; repeat split; lt0 | ].
set (sy := sqrt y); rewrite <- (sqrt_sqrt y); try lt0; unfold sy.
now field; split; lt0.
Qed.

Lemma CVU_y lb  (l0 : 0 < lb < 1) (d : posreal) : d = (1 - lb) / 2 :> R ->
  CVU y_ (fun _ => 1) ((lb + 1)/2) d.
Proof.
intros deq eps ep.
assert (deltap : 0 < eps * lb) by lt0.
destruct (cv_div2 1 (ball 0 (mkposreal _ deltap)) (locally_ball _ _))
  as [N Pn].
exists (N + 1)%nat; simpl.
unfold Boule; intros n y nN inty'.
apply Rabs_lt_between in inty'; simpl in inty'.
assert (nN' : (N <= n)%nat) by lia.
simpl in inty'; assert (inty : 0 < y < 1) by psatzl R.
assert (db := agm_conv 1 y n Rlt_0_1 (proj1 inty) (Rlt_le _ _ (proj2 inty))).
rewrite <- Rabs_Ropp, Ropp_minus_distr', Rabs_pos_eq.
  unfold y_.
  assert (y0 : 0 < y) by psatzl R.
  destruct (ag_le n 1 y Rlt_0_1 (proj1 inty) (Rlt_le _ _ (proj2 inty))).
  assert (v_n0 : 0 < snd (ag 1 y n)) by psatzl R.
  apply Rmult_lt_reg_r with (snd (ag 1 y n));
  [lt0 | rewrite -> Rmult_minus_distr_r, Rmult_1_l].
  unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l, Rmult_1_r;[ | lt0].
  apply Rlt_trans with (eps * lb).
    apply Rle_lt_trans with (1 := db).
    apply Rlt_trans with (1 / 2 ^ n).
      now apply Rmult_lt_compat_r; lt0.
    generalize (Pn n nN').
    rewrite -> ball_Rabs, -> Rminus_0_r, Rabs_pos_eq;[tauto |lt0].
  apply Rmult_lt_compat_l;[lt0 | ].
  apply Rlt_le_trans with y;[psatzl R | ].
  apply Rle_trans with (sqrt (1 * y)).
    rewrite Rmult_1_l.
    apply Rsqr_incr_0;[ | lt0 | lt0].
    rewrite Rsqr_sqrt;[ | lt0]; unfold Rsqr; pattern y at 3.
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat_l; lt0.
  replace (sqrt (1 * y)) with
          (snd (ag 1 y (0 + 1))) by (rewrite plus_0_l; reflexivity).
  assert (ntf : (n = pred n + 1)%nat) by lia.
  rewrite ntf.
  apply Rge_le, (growing_prop (fun n => snd (ag 1 y n)));[ | now lia].
  now intros m; destruct (ag_le' m 1 y); psatzl R.
assert (t := y_gt_1 y n inty); psatzl R.
Qed.

Lemma compare_derive_ag n x : (1 <= n)%nat -> 0 < x < 1 ->
    0 < Derive (u_ n) x < Derive (fun x => snd (ag 1 x n)) x.
Proof.
assert (help : forall a b, 0 < a -> 1 < b / a -> a < b).
  intros a b a0 bda; replace a with (a * 1) by ring.
    replace b with (a * (b / a)) by (field; lt0).
  now apply Rmult_lt_compat_l; lt0.
assert (help2 : forall a b, 0 < a -> a < b -> 1 < b / a).
  intros a b a0 bda; apply Rmult_lt_reg_r with a; try lt0.
  now unfold Rdiv; rewrite -> Rmult_1_l, Rmult_assoc, Rinv_l; lt0.
intros n1 intx; induction n1.
  unfold u_; simpl.
  assert (d1 : Derive (fun x => (1 + x) / 2) x = / 2).
    apply is_derive_unique; evar_last;[auto_derive;[auto | reflexivity] | ].
    now ring.
  assert (d2 : Derive (fun x => sqrt (1 * x)) x = /(2 * sqrt x)).
    apply is_derive_unique; evar_last;[auto_derive;[lt0 | reflexivity ]|].
    rewrite !Rmult_1_l; field; lt0.
  split;[rewrite d1; lt0 |].
  rewrite -> d1, d2; apply Rinv_lt_contravar; try lt0.
  rewrite <- (Rmult_1_r (2)) at 2; rewrite <- sqrt_1 at 5.
  now apply Rmult_lt_compat_l, sqrt_lt_1; lt0.
assert (1 < y_ m x) by now apply y_gt_1.
destruct (ex_derive_ag (S m) x) as [d [e [Pd [Pe Ps]]]]; try lt0.
assert (qd := is_derive_unique _ _ _ Pd).
assert (0 < Derive (u_ (S m)) x).
  destruct (ex_derive_ag (S m) x) as [h [i [Ph [Pi [_ [i0 h0]]]]]]; try lt0.
  now rewrite (is_derive_unique _ _ _ Ph); auto.
split;[auto |].
apply help; auto; try now rewrite qd; auto.
change (_ / _) with (z_ (S m) x); replace (S m) with (m + 1)%nat by ring.
rewrite z_step; auto.
apply Rle_lt_trans with ((1 + 1 * y_ m x) / ((1 + 1) * sqrt (y_ m x))).
  rewrite Rmult_1_l.
  replace 1 with ((1 + 1) / (2 * sqrt 1)) at 1 by (rewrite sqrt_1; field).
  rewrite Rminus_le_0; set (fy := (fun y => (1 + y) / (2 * sqrt y))).
  change (0 <= fy (y_ m x) - fy 1).
  destruct (MVT_gen fy 1 (y_ m x) (fun x => ((x - 1) / (4 * sqrt x ^ 3)))) as
    [c [Pc1 Pc2]]; try rewrite -> Rmin_left, Rmax_right; try lt0.
      now intros; apply derive_y_step; lt0.
    now intros; unfold fy; reg; lt0.
  rewrite Pc2; apply Rmult_le_pos;[ | psatzl R].
  rewrite -> Rmin_left, Rmax_right in Pc1; try psatzl R.
  now apply Rmult_le_pos; lt0.
rewrite Rminus_lt_0.
set (fz := fun z => (1 + z * y_ m x) / ((1 + z) * sqrt (y_ m x))).
change (0 < fz (z_ m x) - fz 1).
assert (1 < z_ m x) by (unfold z_; apply help2; lt0).
destruct (MVT_gen fz 1 (z_ m x)
   (fun z => ((y_ m x - 1) / ((z + 1) ^ 2 * sqrt (y_ m x))))) as
    [c [Pc1 Pc2]]; try rewrite -> Rmin_left, Rmax_right; try lt0.
    now intros; apply derive_z_step; lt0.
  now intros; unfold fz; reg; lt0.
rewrite -> Rmin_left, Rmax_right in Pc1; try lt0.
now rewrite Pc2; repeat apply Rmult_lt_0_compat; lt0.
Qed.

Lemma z_gt_1 x n : 0 < x < 1 -> (1 <= n)%nat -> 1 < z_ n x.
Proof.
intros intx h; induction h.
  unfold z_.
  assert (help : forall a b, 0 < a < b -> 1 < b/a).
    intros a b intab; apply Rmult_lt_reg_r with a;[tauto | ].
    unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l;[ | psatzl R].
    now rewrite -> Rmult_1_l, Rmult_1_r; psatzl R.
  apply help, (compare_derive_ag 1 x); auto.
(* reasoning
 1 + s ^ 2 z/ ((1 + z) s) => 1
 1 + s ^ 2 z => (1 + z) s
 1 - s       => z * (s * (1 - s))
 1           <= z * s
 1/s         <= z *)
replace (S m) with (m + 1)%nat by ring; rewrite z_step; auto.
assert (y1 :=  y_gt_1 x m intx).
assert (0 < (1 + z_ m x) * sqrt (y_ m x)).
 rewrite Rplus_comm; lt0.
apply (Rmult_lt_reg_r ((1 + z_ m x) * sqrt (y_ m x)));[assumption | ].
unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l;[|lt0].
pattern (y_ m x) at 2; rewrite <- pow2_sqrt;[|lt0].
rewrite -> Rmult_plus_distr_r, Rmult_1_l.
apply Rplus_lt_reg_l with (-sqrt(y_ m x) + -sqrt (y_ m x) ^ 2 * z_ m x).
match goal with |- ?a < ?b =>
  replace a with (-(z_ m x * sqrt (y_ m x)) * (sqrt (y_ m x) - 1)) by ring;
  replace b with (-1 * (sqrt (y_ m x) - 1)) by ring
end.
assert (1 < sqrt (y_ m x)).
  now rewrite <- sqrt_1; apply sqrt_lt_1; lt0.
apply Rmult_lt_compat_r;[psatzl R | ].
apply Ropp_lt_contravar; rewrite <- (Rmult_1_r 1).
apply Rmult_le_0_lt_compat; psatzl R.
Qed.

Lemma chain_y_z_y : forall x n, 0 < x < 1 -> (1 <= n)%nat ->
  y_ (n + 1) x <= z_ (n + 1) x <= sqrt (y_ n x).
Proof.
intros x n intx n1.
generalize (y_gt_1 x n intx); intros; assert (0 < y_ n x) by lt0.
assert (sqrt (y_ n x) < y_ n x);[apply sqrt_less; psatzl R | ].
(* TODO : correct sqrt_less in standard library. *)
assert (t := z_gt_1 x n intx n1).
assert (z_ (n + 1) x <= sqrt (y_ n x));[ | split;[|assumption]].
  rewrite z_step; auto.
  unfold Rdiv; rewrite -> Rinv_mult_distr, <- !Rmult_assoc; try lt0.
  apply Rmult_le_reg_r with (sqrt (y_ n x));[lt0 | ].
  rewrite -> !Rmult_assoc, Rinv_l, Rmult_1_r, sqrt_sqrt; try lt0.
  apply Rmult_le_reg_r with (1 + z_ n x);[lt0 | ].
  rewrite -> Rmult_assoc, Rinv_l, Rmult_1_r;[ | lt0].
  apply Rplus_le_reg_r with (- (y_ n x * z_ n x)); ring_simplify; lt0.
rewrite -> y_step, z_step; auto.
apply Rmult_le_reg_r with (2 * (1 + z_ n x) * (sqrt (y_ n x)));[lt0 | ].
unfold yfun; field_simplify;[ | split; lt0| lt0].
unfold Rdiv; rewrite -> Rinv_1, !Rmult_1_r.
apply Rplus_le_reg_r with (- (y_ n x * z_ n x + y_ n x + 1)); ring_simplify.
replace (y_ n x * z_ n x - y_ n x) with (y_ n x * (z_ n x - 1)) by ring.
apply Rle_trans with (1 * (z_ n x - 1) + 1);[psatzl R | ].
apply Rplus_le_compat_r, Rmult_le_compat_r; psatzl R.
Qed.

Lemma CVU_z :
 forall lb ub, 0 < lb < ub -> ub < 1 ->
  forall c (delta : posreal), lb < c - delta -> c + delta < ub ->
  CVU z_ (fun _ => 1) c delta.
Proof.
intros lb ub lu0 u1 c delta c1 c2.
assert (lbint : 0 < lb < 1) by psatzl R.
assert (d0 : 0 < (1 - lb) / 2) by psatzl R.
assert (t := CVU_y lb lbint  (mkposreal _ d0) (refl_equal _)).
intros eps ep; destruct (t _ ep) as [N Pn]; clear t.
exists (S (S N)); intros n y nN dyc.
destruct n as [|n]; [inversion nN | assert (nN' : (N <= n)%nat) by lia ].
assert (inty : 0 < y < 1) by (apply Rabs_lt_between in dyc; psatzl R).
assert (t := y_gt_1 y n inty).
assert (sn1 : (1 <= S n)%nat) by lia.
assert (n1 : (1 <= n)%nat) by lia.
assert (t' := z_gt_1 y  _ inty sn1).
assert (dyc' : Boule ((lb + 1) / 2) (mkposreal _ d0) y).
  now unfold Boule in dyc; apply Rabs_def2 in dyc;
  unfold Boule; simpl; apply Rabs_def1; psatzl R.
generalize (Pn n y nN' dyc'); rewrite <-(Rabs_Ropp (1 - y_ n y)),
 <- (Rabs_Ropp (1 - z_ (S n) y)), !Rabs_pos_eq; try lt0; intros.
generalize (chain_y_z_y y n inty n1), (sqrt_lt (y_ n y) t);
replace (n + 1)%nat with (S n) by ring; intros; psatzl R.
Qed.

Lemma cmp_y_z :
 forall lb, 0 < lb < 1 ->
  exists n_0, forall n, (n_0 <= n)%nat ->
   forall x, lb < x < 1 ->
      (sqrt (y_ n x) - 1) ^ 2 <= (z_ n x - 1) / z_ n x.
Proof.
intros lb l0.
assert (dc : 0 < (1 - lb) / 2) by psatzl R.
destruct (CVU_y lb l0 (mkposreal _ dc) (refl_equal _) (/2))
 as [N1 Pn1];[psatzl R | ].
exists (S (S N1)); intros [ | n] nN1 x intx;[inversion nN1 | ].
assert (nN1' : (N1 <= (n + 1))%nat) by lia.
assert (bx : Boule ((lb + 1)/2) (mkposreal _ dc) x).
  now unfold Boule; simpl; apply Rabs_lt_between; psatzl R.
assert (Pn1' := Pn1 _ _ nN1' bx).
assert (bx' := bx).
apply Rabs_lt_between in bx.
assert (intx' : 0 < x < 1) by psatzl R.
assert (1 < y_ n x) by (apply y_gt_1; assumption).
assert (1 < y_ (n + 1) x) by (apply y_gt_1; assumption).
assert (1 < sqrt (y_ (n + 1) x)) by
 (rewrite <- sqrt_1; apply sqrt_lt_1_alt; psatzl R).
destruct (chain_y_z_y x n intx');[lia | ].
apply Rle_trans with ((z_ (S n) x - 1)/sqrt (y_ n x)).
 apply Rle_trans with ((sqrt (y_ (n + 1) x) - 1)/sqrt (y_ n x)).
  replace (S n) with (n + 1)%nat by ring.
  simpl; rewrite Rmult_1_r; apply Rmult_le_compat_l;[lt0 | ].
 apply Rmult_le_reg_l with (sqrt (y_ n x));[lt0 |rewrite Rinv_r;[ | lt0]].
  assert (nN2 : (N1 <= n)%nat) by lia.
  assert (Pn2 := Pn1 n x nN2 bx').
  rewrite <- Rabs_Ropp, Rabs_pos_eq in Pn2;[|lt0].
  assert (sqrt (y_ n x) < y_ n x) by (apply sqrt_less; psatzl R).
  assert (sqrt (y_ n x) < 2) by psatzl R.
  assert (sqrt (y_ (n + 1) x) - 1 < /2).
   assert (Pn3 := Pn1 _ x nN1' bx').
   rewrite <- Rabs_Ropp, Rabs_pos_eq in Pn3;[|lt0].
   assert (sqrt (y_ (n + 1) x) < y_ (n + 1) x);[ | psatzl R].
   apply sqrt_less; psatzl R.
  replace 1 with (2 */2) by field.
  apply Rmult_le_compat; lt0.
 apply Rmult_le_compat_r;[lt0 | ].
 destruct (chain_y_z_y x (S n) intx');[lia | ].
 assert (sqrt (y_ (n + 1) x) < y_ (n + 1) x).
  apply sqrt_less; psatzl R.
 replace (S n) with (n + 1)%nat by ring; psatzl R.
replace (S n) with (n + 1)%nat by ring.
assert (n11 : (1 <= n + 1)%nat) by lia.
generalize  (z_gt_1 x (n + 1) intx' n11); intros.
apply Rmult_le_compat_l;[psatzl R | ].
apply Rle_Rinv;lt0.
Qed.

Lemma derive_snd_decrease :
 forall lb, 0 < lb < 1 ->
  exists n_0, forall n, (n_0 <= n)%nat ->
   forall x, lb < x < 1 ->
  Derive (fun y =>  snd (ag 1 y (n + 1))) x <=
  Derive (fun y =>  snd (ag 1 y n)) x.
Proof.
intros lb l0.
destruct (cmp_y_z lb l0) as [N Pn].
exists (N + 1)%nat; intros n nN x bx; assert (nN' : (N <= n)%nat) by lia.
assert (n1 : (1 <= n)%nat) by lia.
assert (pintx := bx).
assert ((sqrt (y_ n x) - 1) ^ 2 <= (z_ n x -1)/z_ n x).
 apply (Pn n nN' x bx).
assert (intx : 0 < x < 1) by psatzl R.
destruct (ex_derive_ag n x (proj1 intx)) as
   [vdu [vdv [du [dv [dunn [dvp dup]]]]]].
assert (dup' := n1); apply dup in dup'.
destruct (ex_derive_ag (n + 1) x (proj1 intx)) as
   [vdU [vdV [dU [dV [dUnn [dVp dUp]]]]]].
assert (n2 : (1 <= n + 1)%nat) by lia.
assert (dUp' := n2); apply dUp in dUp'.
(* rewrite -> (is_derive_unique _ _ _ dv). (is_derive_unique _ _ _ dV). *)
assert (main : Derive (u_(n + 1)) x =
             Derive (fun y => snd (ag 1 y n)) x * (z_ n x + 1)/(2 * z_ n x)).
  replace (n + 1)%nat with (S n) by ring.
  rewrite derive_fst_step; [ | now auto ].
  unfold z_, u_; field.
  now rewrite (is_derive_unique _ _ _ du)(is_derive_unique _ _ _ dv); psatzl R.
replace (Derive (fun x => snd (ag 1 x (n + 1))) x) with
    (z_ (n + 1) x * Derive (u_ (n + 1)) x) by
  (unfold z_; field; rewrite (is_derive_unique _ _ _ dU); lt0).
assert (0 < z_ n x) by (assert (t := z_gt_1 x n intx n1); psatzl R).
rewrite main; unfold Rdiv; rewrite Rinv_mult_distr;[ | lt0 | lt0].
rewrite <- !Rmult_assoc, <- (Rmult_comm (Derive _ _)), !Rmult_assoc.
pattern (Derive (fun x => snd (ag 1 x n)) x) at 2; rewrite <- Rmult_1_r.
rewrite (is_derive_unique _ _ _ dv); apply Rmult_le_compat_l;[lt0 | ].
apply Rmult_le_reg_r with (z_ n x);[lt0 | ].
rewrite -> !Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l;[ | lt0].
assert (0 < y_ n x) by (assert (t := (y_gt_1 x n intx)); psatzl R).
rewrite z_step; auto; pattern (y_ n x) at 1; rewrite <- sqrt_sqrt;[ | lt0].
apply (Rmult_le_reg_r ((1 + z_ n x) * sqrt (y_ n x)));[lt0 | ].
unfold Rdiv; rewrite (Rmult_comm (_ * / _)).
rewrite <- (Rmult_assoc _  _ (/ (_ * _))), (Rmult_assoc _ (/ (_ * _))).
rewrite -> Rinv_l, Rmult_1_r; [ | lt0].
match goal with |- ?a <= ?b => apply Rplus_le_reg_l with (Ropp b) end.
rewrite Rplus_opp_l.
match goal with |- ?a <= 0 =>
  replace a with
    ((z_ n x ^ 2 * ((sqrt (y_ n x) - 1) ^ 2 - 1)  +
    z_ n x * ((sqrt (y_ n x) - 1) ^ 2 - 1 + 1)
     + 1) / 2) by field
end.
assert (remove_half : forall a, a <= 0 -> a/2 <= 0) by (intros; psatzl R);
  apply remove_half; clear remove_half.
rewrite -> Rmult_plus_distr_l, !Rmult_minus_distr_l.
apply Rle_trans with
  (z_ n x ^ 2 * ((z_ n x - 1)/z_ n x) - z_ n x ^ 2 +
   z_ n x * ((z_ n x - 1)/z_ n x) + 1).
  rewrite !Rmult_1_r.
  assert (cancel : forall a b, a - b + b = a) by (intros; ring);
   rewrite cancel; clear cancel.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat.
    apply Rplus_le_compat_r.
    now apply Rmult_le_compat_l;[lt0 | assumption].
  now apply Rmult_le_compat_l;[lt0 | assumption].
field_simplify; psatzl R.
Qed.

Lemma u_n_derive_growing n x : 0 < x < 1 ->
    Derive (u_ n) x < Derive (u_ (n + 1)) x.
Proof.
intros intx; destruct n as [|n].
  unfold u_; evar_last; cycle 1.
    now symmetry; apply is_derive_unique; simpl; auto_derive; auto.
  replace (Derive _ _) with 0;[psatzl R | ].
  now symmetry; apply is_derive_unique; evar_last; [auto_derive; auto | ].
destruct (compare_derive_ag (S n) x); try lia; auto.
replace (S n + 1)%nat with (S (S n)) by ring.
rewrite (derive_fst_step (S n)); auto; psatzl R.
Qed.

Lemma ratio_z n x : (1 <= n)%nat -> 0 < x < 1 ->
   1 + z_ n x = 2 * Derive (u_ (S n)) x/Derive (u_ n) x.
Proof.
intros n1 cx.
assert (u'_step : Derive (u_ (S n)) x =
             (Derive (u_ n) x + Derive (fun x => snd (ag 1 x n)) x) / 2).
  rewrite (Derive_ext _ (fun x => /2 * (u_ n x + snd (ag 1 x n)))).
    rewrite Derive_scal; unfold Rdiv; rewrite Rmult_comm.
    apply Rmult_eq_compat_r.
    destruct (ex_derive_ag n x (proj1 cx)) as [d1 [d2 [dd1 [dd2 _]]]].
    now apply Derive_plus;[exists d1 | exists d2]; unfold u_; auto.
  now intros t; unfold u_; rewrite ag_step; simpl; field.
assert (0 < Derive (u_ n) x) by now destruct (compare_derive_ag _ _ n1 cx).
rewrite u'_step; unfold z_; field; psatzl R.
Qed.

Lemma ratio_y n x : 0 < x < 1 ->
  1 + y_ n x = (2 * u_ (S n) x * snd (ag 1 x (S n)) ^ 2 ) /
              (u_ n x * snd (ag 1 x n) ^ 2).
Proof.
intros intx.
assert (t := ag_le n 1 x Rlt_0_1 (proj1 intx) (Rlt_le _ _ (proj2 intx))).
unfold y_, u_; rewrite ag_step; destruct (ag 1 x n) as [a b]; simpl in t |- *.
now rewrite -> Rmult_1_r, sqrt_sqrt; [field |]; lt0.
Qed.

Lemma z_decr x y n : (1 <= n)%nat -> 0 < x < 1 -> 0 < y < 1 -> x < y ->
  z_ n y < z_ n x.
Proof.
intros n1 cx cy xy; induction n1 as [| n pn IHn].
  rewrite !z_1; auto.
  apply Rinv_lt_contravar; try lt0.
  now apply sqrt_lt_1_alt; psatzl R.
assert (ydecr : y_ n y < y_ n x) by now apply y_decr.
assert (ygt1 : 1 < y_ n y) by (assert (tmp := y_gt_1 y n cy); psatzl R).
assert (zgt1 : 1 < z_ n y) by (assert (tmp := z_gt_1 y n cy pn); psatzl R).
replace (S n) with (n + 1)%nat by ring; rewrite !z_step; try lia; try psatzl R.
apply Rlt_trans with ((1 + z_ n y * y_ n x) / ((1 + z_ n y) * sqrt (y_ n x))).
  set zfun1 := fun w => (1 + z_ n y * w) / ((1 + z_ n y) * sqrt w).
  change (zfun1 (y_ n y) < zfun1 (y_ n x)).
set (zfund1 :=  fun c' => (z_ n y ^ 2 * c' + z_ n y * c' - z_ n y - 1) /
   (2 * z_ n y ^ 2 * sqrt c' ^ 3 + 4 * z_ n y * sqrt c' ^ 3 +
    2 * sqrt c' ^ 3)).
(* TODO : streamline statement of MVT_cor2, which should not use
     derivable_pt_lim. *)
  assert (zfund : forall c, y_ n y <= c <= y_ n x ->
             derivable_pt_lim zfun1 c (zfund1 c)).
    intros c cc; rewrite <- is_derive_Reals.
    unfold zfun1, zfund1; auto_derive; repeat split; try lt0.
    field_simplify; repeat split; try lt0.
    replace (sqrt c ^ 2) with c.
      now simpl; field; lt0.
    now simpl; rewrite -> Rmult_1_r, sqrt_sqrt; psatzl R.
  destruct (MVT_cor2 zfun1 zfund1 (y_ n y) (y_ n x) ydecr zfund)
    as [c [pc cc]].
  apply Rplus_lt_reg_r with (- zfun1 (y_ n y)); rewrite Rplus_opp_r.
  unfold Rminus in pc; rewrite pc.
  assert (0 < zfund1 c).
    unfold zfund1.
    assert (0 < z_ n y ^ 2 * c + z_ n y * c - z_ n y - 1).
      apply Rlt_trans with (z_ n y ^ 2 * 1 + z_ n y * 1 - z_ n y - 1).
        match goal with |- 0 < ?a =>
          replace a with ((z_ n y + 1) * (z_ n y - 1) )by ring
        end; lt0.
      unfold Rminus; repeat apply Rplus_lt_compat_r; apply Rplus_lt_compat.
        apply Rmult_lt_compat_l; lt0.
      apply Rmult_lt_compat_l; lt0.
    lt0.
  lt0.
set (zfun2 := fun w => (1 + w * y_ n x) / ((1 + w) * sqrt (y_ n x))).
set (zfund2 := fun c => ((y_ n x  - 1) * sqrt (y_ n x)) /
                      ((c + 1) * sqrt (y_ n x)) ^ 2).
change (zfun2 (z_ n y) < zfun2 (z_ n x)).
assert (zfund' :
    forall c, z_ n y <= c <= z_ n x -> derivable_pt_lim zfun2 c (zfund2 c)).
  intros c cc; unfold zfun2, zfund2; auto_derive; try lt0.
  simpl; field; repeat split; lt0.
destruct (MVT_cor2 zfun2 zfund2 (z_ n y) (z_ n x) IHn zfund')
    as [c [pc cc]].
apply Rplus_lt_reg_r with (- zfun2 (z_ n y)); rewrite Rplus_opp_r.
unfold Rminus in pc; rewrite pc.
assert (0 < zfund2 c) by (unfold zfund2; lt0).
lt0.
Qed.

Lemma d_u_decr n x y : (1 <= n)%nat -> 0 < x < 1 -> 0 < y < 1 -> x < y ->
  0 < Derive (u_ n) y <= Derive (u_ n) x.
Proof.
intros n1 cx cy xy.
induction n1 as [ | n pn IHn].
  assert (d1 : forall x', Derive (u_ 1) x' = /2).
    intros x'; apply is_derive_unique.
    apply (is_derive_ext (fun x => (1 + x)/2)).
      now intros; unfold u_; simpl.
    now auto_derive; auto; simpl; ring.
  now rewrite !d1; psatzl R.
assert (1 < z_ n y) by now apply z_gt_1.
split.
  replace (Derive (u_ (S n)) y) with
       ((2 * Derive (u_ (S n)) y / Derive (u_ n) y) * Derive (u_ n) y / 2);
    [ | field; psatzl R].
  assert (0 < (1 + z_ n y) / 2) by psatzl R.
  now rewrite <- ratio_z; lt0.
replace (Derive (u_ (S n)) y) with
     ((2 * Derive (u_ (S n)) y / Derive (u_ n) y) * Derive (u_ n) y / 2);
  [rewrite <- ratio_z; auto | field; psatzl R].
replace (Derive (u_ (S n)) x) with
     ((2 * Derive (u_ (S n)) x / Derive (u_ n) x) * Derive (u_ n) x / 2);
  [rewrite <- ratio_z; auto | field; psatzl R].
apply Rle_trans with ((1 + z_ n y) / 2 * Derive (u_ n) x).
  now unfold Rdiv; rewrite !Rmult_assoc; apply Rmult_le_compat_l; lt0.
unfold Rdiv; rewrite -> Rmult_assoc, (Rmult_comm (/ 2)), <- Rmult_assoc.
repeat apply Rmult_le_compat_r; try lt0.
assert (tmp := z_decr x y n pn cx cy xy); psatzl R.
Qed.

Lemma cv_du :
  forall lb (d : posreal), 0 < lb < 1 -> d = (1 - lb) / 2 :> R ->
  CVU (fun n x => Derive (u_ n) x)
  (fun x => Lim_seq (fun n => Derive (u_ n) x))
  ((lb + 1) / 2) d.
Proof.
intros lb d lbint deq eps epspos.
assert (cl0 : 0 < lb/3) by psatzl R.
assert (cl2 : lb/3 < 1) by psatzl R.
assert (cl1 : (lb + 2) / 3 < 1) by psatzl R.
assert (l1 : lb / 3 < (lb + 2) / 3) by psatzl R.
assert (l0 : 0 < lb / 3) by psatzl R.
assert (d0 : 0 < ((2 * lb + 1) / 3 - (2 * lb / 3)) / 2) by psatzl R.
assert (c1 : lb / 3 < (2 * lb / 3 + ((2 * lb + 1) / 3)) / 2 -
             mkposreal _ d0).
  simpl; psatzl R.
assert (c2 : (2 * lb / 3 + ((2 * lb + 1) / 3))/ 2 + mkposreal _ d0 <
             (lb + 2) / 3).
  simpl; psatzl R.
destruct (derive_snd_decrease _ (conj cl0 cl2)) as [N0 Pn0].
assert (eps'0 : 0 < eps / Derive (fun x => snd (ag 1 x (N0 + 2))) lb).
  assert (tmp1 : (1 <= N0 + 2)%nat) by lia.
  now destruct (compare_derive_ag _ _ tmp1 lbint); lt0.
set (eps' := mkposreal _ eps'0).
destruct (CVU_z _ _ (conj l0 l1) cl1 _ _ c1 c2 _ (cond_pos eps'))
  as [N1 Pn1].
set (N := max N1 N0).
assert (forall n, (N1 <= n)%nat -> Rabs (1 - z_ n lb) < eps').
  intros n nn; apply Pn1; auto.
  unfold Boule; simpl; rewrite Rabs_lt_between; split; psatzl R.
assert (cmpdlb :
    Derive (fun x => snd (ag 1 x (N + 2))) lb - Derive (u_ (N + 2)) lb <
             eps).
  assert (dN0 : 0 < Derive (u_ (N + 2)) lb).
    assert (tmp1 : (1 <= N + 2)%nat) by lia.
    now destruct (compare_derive_ag _ _ tmp1 lbint); lt0.
  apply Rmult_lt_reg_r with (/Derive (u_ (N + 2)) lb); try lt0.
  rewrite -> Rmult_minus_distr_r, Rinv_r;[ | lt0].
  apply Rlt_trans with (eps / Derive (fun x => snd (ag 1 x (N0 + 2))) lb); cycle 1.
    apply Rmult_lt_compat_l;[now auto | ].
      apply Rinv_lt_contravar.
      apply Rmult_lt_0_compat; auto.
      assert (tmp1 : (1 <= N0 + 2)%nat) by lia.
      now destruct (compare_derive_ag _ _ tmp1 lbint); psatzl R.
    apply Rlt_le_trans with (Derive (fun x => snd (ag 1 x (N + 2))) lb).
      assert (tmp1 : (1 <= N + 2)%nat) by lia.
      now destruct (compare_derive_ag _ _ tmp1 lbint); lt0.
    assert (tmp1 : (N0 + 2 <= N + 2)%nat).
      now unfold N; assert (tmp1 := Nat.le_max_r N1 N0); lia.
    clear dN0; induction tmp1 as [ | m lem IHm].
      now auto with real.
    apply Rle_trans with (2 := IHm).
    replace (S m) with ((m + 1)%nat) by ring.
    now apply Pn0; try lia; psatzl R.
  match goal with |- ?a < _ => rewrite <- (Rabs_right a) end.
    rewrite <- Rabs_Ropp, Ropp_minus_distr.
  apply (Pn1 (N + 2)%nat lb).
      now unfold N; assert (tmp1 := Nat.le_max_l N1 N0); lia.
    now unfold Boule; simpl; rewrite Rabs_lt_between; psatzl R.
  assert (tmp1 : (1 <= N + 2)%nat) by lia.
  assert (tmp := z_gt_1 lb (N + 2) lbint tmp1); unfold z_, Rdiv in tmp.
  now psatzl R.
exists (N + 2)%nat; intros n x nn intx.
assert (n1 : (1 <= n)%nat) by lia.
assert (intx' : lb < x < 1).
  now unfold Boule in intx; apply Rabs_def2 in intx; psatzl R.
assert (intx'' : 0 < x < 1).
  now psatzl R.
assert (ub_lim :  Rbar_le (Lim_seq (fun n0 => Derive (u_ n0) x))
                (Lim_seq (fun _ => Derive (fun y => snd (ag 1 y n)) x))).
  apply Lim_seq_le_loc.
  exists n; intros m mn;
  apply Rle_trans with (Derive (fun y => snd (ag 1 y m)) x).
    assert (tmp1 : (1 <= m)%nat) by lia.
    now assert (tmp := compare_derive_ag m x tmp1 intx''); psatzl R.
  induction mn as [ | m nlem IHm]; auto with real.
  apply Rle_trans with (2 := IHm); replace (S m) with (m + 1)%nat by ring.
  apply Pn0.
    apply le_trans with (2 := nlem), le_trans with (2 := nn).
    now unfold N; assert (tmp1 := Nat.le_max_r N1 N0); lia.
  now psatzl R.
assert (lb_lim : Rbar_le
                (Lim_seq (fun _ => Derive (u_ n) x))
                (Lim_seq (fun n0 => Derive (u_ n0) x))).
  apply Lim_seq_le_loc.
  exists n; intros m; induction 1 as [| m nlem IHm]; auto with real.
  apply Rle_trans with (1 := IHm), Rlt_le.
  replace (S m) with (m + 1)%nat by ring.
  now apply u_n_derive_growing.
apply Rle_lt_trans with (Rabs (Derive (fun x => snd (ag 1 x n)) x -
                              Derive (u_ n) x)).
  rewrite !Rabs_right.
      apply Rplus_le_compat_r.
      revert ub_lim lb_lim; rewrite !Lim_seq_const.
      now case_eq (Lim_seq (fun n0 => Derive (u_ n0) x)); [simpl; auto | | ].
    assert (tmp1 : (1 <= n)%nat) by lia.
    now assert (tmp := compare_derive_ag n x tmp1 intx''); psatzl R.
  rewrite Lim_seq_const in lb_lim; rewrite Lim_seq_const in ub_lim.
   simpl in lb_lim; simpl in ub_lim.
  destruct (Lim_seq (fun n => Derive (u_ n) x)) as [r | | ].
      now simpl; psatzl R.
    now simpl in ub_lim.
  easy.
assert (cmpd : 0 < Derive (u_ n) x < Derive (fun y => snd (ag 1 y n)) x).
  now apply compare_derive_ag.
rewrite Rabs_right;[ | psatzl R].
apply Rle_lt_trans with (2 := cmpdlb).
assert (cmplb : 0 < Derive (u_ (N + 2)) lb <
           Derive (fun y => snd (ag 1 y (N + 2))) lb).
  now assert (tmp1 : (1 <= N + 2)%nat) by lia; apply compare_derive_ag.
match goal with |- ?a <= ?b =>
  replace a with ((1 - /z_ n x) *
                 Derive (fun y => snd(ag 1 y n)) x) by (unfold z_; field; lt0);
  replace b with ((1 - /z_ (N + 2) lb) *
                  Derive (fun y => snd (ag 1 y (N + 2))) lb)
     by (unfold z_; field; lt0)
end.
apply Rle_trans with ((1 - /z_ n lb) * Derive (fun y => snd(ag 1 y n)) lb);
cycle 1.
  assert (H1 := z_gt_1 _ _ lbint n1).
  apply Rmult_le_compat.
        apply Rmult_le_reg_r with (z_ n lb); try psatzl R.
        rewrite -> Rmult_0_l, Rmult_minus_distr_r, Rinv_l; psatzl R.
      assert (tmp := compare_derive_ag _ _ n1 lbint); psatzl R.
    apply Rplus_le_compat_l, Ropp_le_contravar, Rinv_le_contravar.
      psatzl R.
    clear -nn lbint intx''; induction nn as [|m nlem IHm];[auto with real |].
    apply Rle_trans with (2 := IHm).
    assert (exists k, (m = k + 1)%nat) as [m' qm'].
      now clear -nlem; destruct m as [| k]; try lia; exists k; ring.
    apply Rle_trans with (y_ m lb); cycle 1.
      assert (tmp1 : (1 <= m')%nat) by lia.
      now rewrite qm'; assert (tmp := chain_y_z_y _ _ lbint tmp1); psatzl R.
    apply Rle_trans with (sqrt (y_ m lb)).
      replace (S m) with (m + 1)%nat by ring.
      assert (tmp1 : (1 <= m)%nat) by lia.
      now assert (tmp := chain_y_z_y _ _ lbint tmp1); tauto.
    now apply Rlt_le, sqrt_lt, y_gt_1.
  clear -Pn0 nn intx' lbint; induction nn as [|m nlem IHm];[auto with real | ].
  apply Rle_trans with (2 := IHm); replace (S m) with (m + 1)%nat by ring.
  apply Pn0; auto; try psatzl R; apply le_trans with (2 := nlem).
  now assert (tmp := Nat.le_max_r N1 N0); unfold N; lia.
apply Rmult_le_compat.
        assert (tmp:= z_gt_1 _ _ intx'' n1).
        apply Rmult_le_reg_r with (z_ n x);[psatzl R|].
        now rewrite -> Rmult_0_l, Rmult_minus_distr_r, Rinv_l; psatzl R.
      now psatzl R.
    apply Rlt_le, Rplus_lt_compat_l, Ropp_lt_contravar, Rinv_lt_contravar.
      assert (H1 := conj (z_gt_1 _ _ lbint n1) (z_gt_1 _ _ intx'' n1)).
      now lt0.
    now apply z_decr.
match goal with
  |- ?a <= ?b => replace a with (z_ n x * Derive (u_ n) x);
    [| unfold z_; field;
       assert (tmp := compare_derive_ag _ _ n1 intx''); psatzl R];
    replace b with (z_ n lb * Derive (u_ n) lb);
    [| unfold z_; field;
       assert (tmp := compare_derive_ag _ _ n1 lbint); psatzl R]
end; cycle 1.
apply Rmult_le_compat.
      now assert (tmp:= z_gt_1 _ _ intx'' n1); psatzl R.
    now assert (tmp := compare_derive_ag _ _ n1 intx''); psatzl R.
  now apply Rlt_le, z_decr; tauto.
now apply d_u_decr; tauto.
Qed.

Lemma ex_derive_ff x : 0 < x < 1 -> ex_derive ff x.
Proof.
intros intx; set (lb := x / 2).
assert (lbin : 0 < lb < 1) by (unfold lb; psatzl R).
assert (dpos : 0 < (1 - lb) / 2) by psatzl R.
set (d := mkposreal _ dpos).
assert (dq : pos d = (1 - lb) / 2) by reflexivity.
assert (xinb : Boule ((lb + 1) / 2) d x).
  now unfold Boule; apply Rabs_def1; unfold d, lb; simpl; psatzl R.
assert (cv_u : forall x, Boule ((lb + 1) / 2) d x ->
               Un_cv (fun n => u_ n x) (ff x)).
  intros x' bx' eps ep0.
  apply Rabs_def2 in bx'.
  assert (dpos' : 0 < (1 - x / 2) / 2) by psatzl R.
  set (d' := mkposreal _ dpos').
  assert (d'q : d' = (1 - x / 2) / 2 :> R) by reflexivity.
  destruct (cvu_u_ff x intx d' d'q eps ep0) as [N Pn]; exists N.
  intros n Nn; rewrite R_dist_sym; apply Pn; auto.
  now apply Rabs_def1; simpl; assert (lb = x / 2) by reflexivity; psatzl R.
assert (dv_u : forall n x, Boule ((lb + 1) / 2) d x ->
               derivable_pt_lim (u_ n) x (Derive (u_ n) x)).
  intros n x' bx'.
  assert (x'0 : 0 < x') by now apply Rabs_def2 in bx'; psatzl R.
  rewrite <- is_derive_Reals; apply Derive_correct.
  destruct (ex_derive_ag n x' x'0) as [d1 [d2 [Pd1 _]]].
  now exists d1; exact Pd1.
assert (t :=
         CVU_derivable u_ _ ff _
         _ d (cv_du _ _ lbin dq) cv_u dv_u).
  now eapply ex_intro; rewrite is_derive_Reals; apply t.
Qed.

Lemma cv_u_ff' (lb : R) (d : posreal) :
  0 < lb < 1 -> d = (1 - lb) / 2 :> R ->
   CVU (fun n => Derive (u_ n)) (Derive ff) ((lb + 1) / 2) d.
Proof.
intros lbint deq.
apply CVU_ext_lim with (fun y => real (Lim_seq (fun n => Derive (u_ n) y))).
  now apply cv_du.
assert (tmp1 := cv_du lb d lbint deq).
assert (tmp2 : forall x, Boule ((lb + 1) / 2) d x ->
               Un_cv (fun n => u_ n x) (ff x)).
  unfold Boule; intros x cx; apply Rabs_def2 in cx.
  assert (xp : 0 < x) by psatzl R.
  assert (dpos : 0 < (1 - x / 2) / 2) by psatzl R.
  apply (CVU_cv u_ ff ((1 + x / 2) / 2) (mkposreal _ dpos)).
    now apply cvu_u_ff; simpl; psatzl R.
  now apply Rabs_def1; simpl; psatzl R.
assert (tmp3 : forall n x, Boule ((lb + 1) / 2) d x ->
               derivable_pt_lim (u_ n) x (Derive (u_ n) x)).
  unfold Boule; intros n x cx; apply Rabs_def2 in cx.
  rewrite <- is_derive_Reals.
  assert (xp : 0 < x) by psatzl R.
  destruct (ex_derive_ag n x xp) as [du [dv [isdu _]]].
  now apply Derive_correct; exists du; apply isdu.
assert
  (tmp := CVU_derivable u_ (fun n => Derive (u_ n)) ff
          (fun x => Lim_seq (fun n => Derive (u_ n) x)) ((lb + 1) / 2) d tmp1
          tmp2 tmp3); clear tmp1 tmp2 tmp3.
intros x cx.
symmetry; apply is_derive_unique; rewrite is_derive_Reals.
now apply tmp.
Qed.

Lemma continuous_ff x : 0 < x < 1 -> continuous ff x.
Proof.
now intros intx; apply (ex_derive_continuous ff), ex_derive_ff.
Qed.

Lemma derive_ff_pos x : 0 < x < 1 -> 0 < Derive ff x.
Proof.
intros intx; apply Rlt_le_trans with (/2); [lt0 | ].
assert (lim_du : is_lim_seq (fun n => Derive (u_ n) x) (Derive ff x)).
  assert (xhalf0 : 0 < x / 2 < 1) by psatzl R.
  assert (dpos : 0 < (1 - x / 2) / 2) by psatzl R.
  rewrite is_lim_seq_Reals;
  apply (CVU_cv (fun n => Derive (u_ n)) (Derive ff) ((x / 2 + 1) / 2)
             (mkposreal _ dpos)).
    apply (cv_u_ff' (x / 2) (mkposreal _ dpos) xhalf0 (refl_equal _)).
  apply Rabs_def1; simpl; psatzl R.
assert (du_1 : Derive (u_ 1) x = / 2).
  unfold u_; simpl; apply is_derive_unique; auto_derive; lt0.
rewrite <- du_1.
apply (is_lim_seq_incr_compare (fun n => Derive (u_ n) x)); auto.
intros n; replace (S n) with (n + 1)%nat by ring.
now apply Rlt_le, u_n_derive_growing.
Qed.

(* End of derivability for ff. *)

Lemma w0 n x : 0 < x < 1 -> 0 < w_ n x.
Proof.
intros intx; unfold w_; apply sqrt_lt_R0.
assert (t := ag_lt n _ _ intx).
destruct (ag_le n 1 x); try lt0.
now rewrite (_ : forall u v, u ^ 2 - v ^ 2 = (u - v) * (u + v));
   [lt0| intros; ring].
Qed.

Lemma is_derive_w n x : 0 < x < 1 ->
  is_derive (w_ n) x
   (/ (2 * sqrt (u_ n x ^ 2 - snd (ag 1 x n) ^ 2)) *
              (2 * u_ n x * Derive (u_ n) x -
               2 * snd (ag 1 x n) *
               Derive (fun x => snd (ag 1 x n)) x)).
Proof.
intros [x0 x1]; unfold w_.
  rewrite Rmult_comm; apply (is_derive_comp sqrt).
  assert (t := ag_le n 1 x Rlt_0_1 x0).
  assert (t' := ag_lt n 1 x (conj x0 x1)).
  auto_derive.
    enough (snd (ag 1 x n) ^ 2 < fst (ag 1 x n) ^ 2) by psatzl R.
    now apply Rmult_le_0_lt_compat; lt0.
  now rewrite (_ : forall u v, u ^ 2 - v ^ 2 = (u - v) * (u + v));
   [lt0| intros; ring].
destruct (ex_derive_ag n x) as [d1 [d2 [Pd1 [Pd2 cmps]]]]; try lt0.
unfold u_; apply: is_derive_minus.
  evar_last.
  apply (is_derive_comp (fun x => x ^ 2) (fun x => fst (ag 1 x n))).
    apply is_derive_pow; apply is_derive_id.
    now apply Derive_correct; exists d1; auto.
  simpl; unfold scal; simpl; unfold mult, one; simpl; ring.
evar_last.
apply (is_derive_comp (fun x => x ^ 2) (fun x => snd (ag 1 x n))).
  apply is_derive_pow; apply is_derive_id.
  now apply Derive_correct; exists d2; auto.
simpl; unfold scal; simpl; unfold mult, one; simpl; ring.
Qed.

Lemma is_derive_k n x : 0 < x < 1 -> is_derive (k_ n) x
     (/(2 ^ n) * (/(u_ n x / w_ n x) *
         ((Derive (u_ n) x * w_ n x - Derive (w_ n) x * u_ n x) /
         (w_ n x) ^ 2))).
Proof.
intros intx; unfold k_.
assert (0 < w_ n x) by now apply w0.
assert (0 < u_ n x) by (destruct (ag_le n 1 x Rlt_0_1); unfold u_; lt0).
auto_derive;[ | field_simplify; try rewrite (Rmult_comm (Derive _ _) (w_ _ _));
                try reflexivity; repeat split; lt0].
destruct (ex_derive_ag n x) as [d1 [d2 [Pd1 [Pd2 cmps]]]]; try lt0.
split;[exists d1; exact Pd1 | repeat split; try lt0].
unfold w_; apply ex_derive_comp.
  auto_derive.
  assert (t := ag_lt n 1 x intx); destruct (ag_le n 1 x); try lt0.
  now rewrite (_ : forall u v, u ^ 2 - v ^ 2 = (u - v) * (u + v));
   [lt0| intros; ring].
now apply: ex_derive_minus; apply ex_derive_pow;
 solve [exists d1; auto | exists d2; auto].
Qed.

Lemma w_simpl : forall x n, 0 < x < 1 ->
   w_(n + 1) x = (u_ n x - snd (ag 1 x n))/2.
Proof.
intros x n intx; replace (n + 1)%nat with (S n) by ring; unfold w_.
destruct (ag_le n 1 x); try lt0; generalize (w0 n _ intx).
replace (S n) with (1 + n)%nat by ring.
unfold u_, w_; rewrite ag_shift; simpl ag.
destruct (ag 1 x n) as [a' b']; unfold fst, snd in * |- *.
intros dif; assert (dif' := dif).
apply (pow_lt _ 2) in dif; rewrite sqrt_pow_2 in dif; cycle 1.
  enough (b' ^ 2 <= a' ^ 2) by psatzl R.
  now apply pow_incr; psatzl R.
rewrite <- !Rsqr_pow2 in dif.
assert (t : forall A B, 0 < A - B -> B < A) by (intros; psatzl R).
apply t in dif; apply Rsqr_incrst_0 in dif; try lt0; clear t.
rewrite pow2_sqrt;[ | lt0].
match goal with
  |- context [sqrt ?A] => replace A with (((a' - b')/2) ^ 2) by field
end.
rewrite sqrt_pow2; psatzl R.
Qed.

Lemma derive_k_div_snd_ag n x : 0 < x < 1 ->
   Derive (k_ n) x/snd (ag 1 x n) ^ 2 =
         Derive (k_ (S n)) x/snd (ag 1 x (S n)) ^ 2.
Proof.
intros intx.
destruct (ag_le n 1 x); try lt0.
assert (cmp := ag_lt n 1 x intx).
assert (t := is_derive_k n x intx).
rewrite (is_derive_unique (k_ n) x _ t); clear t.
assert (t := is_derive_w n x intx).
rewrite (is_derive_unique (w_ n) x _ t); clear t.
assert (eqf : forall x, 0 < x < 1 ->
           / (2 ^ (S n)) * ln ((u_ n x + snd (ag 1 x n))
              / (u_ n x - snd (ag 1 x n)))
         = k_ (S n) x).
  intros y inty; unfold k_; symmetry.
  replace (u_ (S n) y) with ((u_ n y + snd(ag 1 y n)) / 2); cycle 1.
    now unfold u_; replace (S n) with (1 + n)%nat by ring; rewrite ag_shift.
  replace (S n) with (n + 1)%nat by ring; rewrite w_simpl;[ | assumption].
  repeat apply f_equal; field.
  now unfold u_; assert (t := ag_lt n _ _ inty); psatzl R.
assert (derf : is_derive
          (fun x => /(2 ^ S n) * ln ((u_ n x + snd (ag 1 x n)) /
                (u_ n x - snd(ag 1 x n))))
          x
          (/(2 ^ S n) * (/((u_ n x + snd (ag 1 x n))/
            (u_ n x - snd(ag 1 x n))) *
           (((Derive (u_ n) x + Derive (fun y => snd (ag 1 y n)) x)
            * (u_ n x - snd (ag 1 x n)) -
            (Derive (u_ n) x - Derive (fun y => snd (ag 1 y n)) x) *
              (u_ n x + snd (ag 1 x n)))/
            (u_ n x - snd (ag 1 x n))^ 2)))).
  destruct (ex_derive_ag n x) as [d1 [d2 [Pd1 [Pd2 cmps]]]]; try lt0.
  apply is_derive_scal.
  rewrite Rmult_comm; apply (is_derive_comp ln).
    rewrite is_derive_Reals; apply derivable_pt_lim_ln.
    now (unfold u_; lt0).
  evar_last.
    apply (is_derive_div (fun x => u_ n x + snd(ag 1 x n))
            (fun x => u_ n x - snd (ag 1 x n)) _
            (Derive (u_ n) x + Derive (fun y => snd (ag 1 y n)) x)
            (Derive (u_ n) x - Derive (fun y => snd (ag 1 y n)) x)).
        now apply: is_derive_plus;
          apply Derive_correct; solve[exists d1; auto|exists d2; auto].
      now apply: is_derive_minus;
          apply Derive_correct; solve[exists d1; auto|exists d2; auto].
    now unfold u_; lt0.
  field; unfold u_; lt0.
replace (Derive (k_ (S n)) x) with
           (/(2 ^ S n) * (/((u_ n x + snd (ag 1 x n)) /
                (u_ n x - snd (ag 1 x n))) *
           (((Derive (u_ n) x + Derive (fun y => snd (ag 1 y n)) x) *
              (u_ n x - snd (ag 1 x n)) -
            (Derive (u_ n) x - Derive (fun y => snd (ag 1 y n)) x) *
             (u_ n x + snd (ag 1 x n))) /
            (u_ n x - snd (ag 1 x n))^ 2))); cycle 1.
  symmetry; apply is_derive_unique.
  apply (is_derive_ext_loc (fun x : R_AbsRing => / 2 ^ S n *
          ln ((u_ n x + snd (ag 1 x n)) / (u_ n x - snd (ag 1 x n))))); cycle 1.
    exact derf.
  assert (m0 : 0 < Rmin x (1 - x)) by (apply Rmin_glb_lt; lt0).
  exists (mkposreal _ m0); simpl; intros y bay; apply eqf.
  revert bay; rewrite ball_Rabs.
  destruct (Rle_dec x y).
    rewrite Rabs_right; try lt0; intros bay.
    now split;[| assert (t := Rmin_r x (1 - x))]; lt0.
  rewrite Rabs_left; try lt0; intros bay.
  now split;[assert (t := Rmin_l x (1 - x)) |];lt0.
change (sqrt (u_ n x ^ 2 - snd (ag 1 x n) ^ 2)) with (w_ n x).
replace (snd (ag 1 x (S n))) with (sqrt (fst (ag 1 x n) * snd (ag 1 x n)));
  cycle 1.
  now replace (S n) with (1 + n)%nat by ring; rewrite ag_shift.
rewrite sqrt_pow_2; try lt0.
change (2 ^ S n) with (2 * 2 ^ n).
apply Rminus_diag_uniq; unfold u_; field_simplify; cycle 1.
  now unfold u_; repeat split; try lt0; apply Rgt_not_eq, w0.
replace (w_ n x ^ 2) with (u_ n x ^ 2 - snd (ag 1 x n) ^ 2); cycle 1.
  unfold w_; rewrite sqrt_pow_2; [reflexivity | ].
  now rewrite <- Rminus_le_0; apply pow_incr; psatzl R.
unfold u_; field_simplify; try (unfold Rdiv; rewrite !Rmult_0_l; reflexivity).
rewrite <- !(Rmult_comm (u_ n x ^ 2 - snd (ag 1 x n) ^ 2)),
    !Rmult_assoc, <- !Rmult_minus_distr_l.
apply Rgt_not_eq;repeat apply Rmult_lt_0_compat; try lt0.
replace (u_ n x ^ 2 - snd (ag 1 x n) ^ 2) with
    ((u_ n x - snd (ag 1 x n)) * (u_ n x + snd (ag 1 x n))) by ring.
  now unfold u_; lt0.
replace (fst (ag 1 x n) ^ 3 * snd (ag 1 x n) ^ 2 -
             fst (ag 1 x n) * snd (ag 1 x n) ^ 4) with
     ((fst (ag 1 x n) * snd (ag 1 x n) ^ 2) *
       (fst (ag 1 x n)  - snd (ag 1 x n)) * (fst (ag 1 x n) + snd (ag 1 x n)))
    by ring; lt0.
Qed.

Lemma Derive_k x n : 0 < x < 1 ->
  Derive (k_ n) x = snd (ag 1 x n) ^ 2 / (x * (1 - x ^ 2)).
Proof.
intros intx; assert (0 < x * x < 1).
 split;[| replace 1 with (1 * 1) by ring; apply Rmult_le_0_lt_compat]; lt0.
induction n.
  rewrite (is_derive_unique _ _ _ (is_derive_k 0 x intx)).
  unfold w_, u_, Rdiv; simpl.
  rewrite -> !Rmult_1_r, Rinv_1, !Rmult_1_l, Derive_const, Rmult_0_l.
  replace (Derive (fun x0 => sqrt (1 - x0 * (x0 * 1))) x) with
   (/(2 * (sqrt (1 - x * (x * 1)))) * (0 - INR 2 * x ^ 1)).
    simpl; rewrite !Rmult_1_r; field_simplify; try psatzl R; try lt0.
    rewrite pow2_sqrt;[ | psatzl R].
    now field; simpl; rewrite Rmult_1_r; psatzl R.
  symmetry; apply is_derive_unique.
  evar_last.
    apply is_derive_sqrt.
      apply: is_derive_minus.
        now apply is_derive_const.
      now apply (is_derive_pow _ 2), is_derive_id.
    now rewrite Rmult_1_r; lt0.
  now simpl; unfold minus, plus, opp, zero, one; simpl; field; lt0.
replace (Derive (k_ (S n)) x) with
  ((Derive (k_ n) x / snd (ag 1 x n) ^ 2) * snd (ag 1 x (S n)) ^ 2).
  now rewrite IHn; field; destruct (ag_le n 1 x); lt0.
rewrite derive_k_div_snd_ag; auto; field; destruct (ag_le (S n) 1 x); lt0.
Qed.

Lemma bound_modulus_convergence_snd_ag n x:
  0 < x < 1 -> 0 <= ff x - snd (ag 1 x n) <= Rabs(1 - x)/2^n.
Proof.
intros intx; assert (x0 : 0 < x) by lt0.
assert (tmp := agm_conv 1 x n Rlt_0_1 x0 (Rlt_le _ _ (proj2 intx))).
destruct (ag_le n 1 x); try lt0.
rewrite Rabs_right; try lt0.
unfold ff; rewrite <- (M_shift 1 x n); try lt0.
unfold ff; destruct (Mbounds (fst (ag 1 x n)) (snd (ag 1 x n))); lt0.
Qed.

Lemma M_ag_diff_squares_step : (* does not depend on any lemma after ag_lt *)
  forall a b n, 0 < a -> 0 < b -> b < a ->
    M (fst (ag a b (S n)))
             (sqrt (fst (ag a b (S n)) ^ 2 - snd (ag a b (S n)) ^ 2)) =
    /2 *  M (fst (ag a b n)) (sqrt (fst (ag a b n) ^ 2 - snd (ag a b n) ^ 2)).
Proof.
intros a b n a0 b0 ba.
assert (pos_ag := ag_le n a b a0 b0 (Rlt_le _ _ ba)).
assert (dif := ag_lt n a b (conj b0 ba)).
assert (dif2 := ag_lt (S n) a b (conj b0 ba)); revert dif2.
rewrite ag_step.
destruct (ag a b n) as [an bn]; simpl in pos_ag, dif; simpl fst; simpl snd.
intros dif2.
assert (help : forall A B, 0 < B < A -> 0 < A ^ 2 - B ^ 2).
  intros A B H; replace (A ^ 2 - B ^ 2) with ((A - B) * (A + B)) by ring; lt0.
assert (bn0 : 0 < bn) by psatzl R.
assert (0 < an ^ 2 - bn ^ 2) by (apply help; lt0).
assert (d1 : 0 < sqrt (an * bn)) by lt0.
assert (d2 := help _ _ (conj d1 dif2)).
rewrite <- (M_shift ((an + bn) / 2) _ 1);[| |apply sqrt_lt_R0]; try lt0.
unfold ag, fst, snd; rewrite sqrt_pow_2; try lt0.
replace (((an + bn)/2) ^ 2 - an * bn) with (((an - bn)/2) ^ 2) by field.
rewrite sqrt_pow2;[|psatzl R].
replace ((an + bn) / 2 + (an - bn) / 2) with an by field.
replace ((an + bn)/2 * ((an - bn) / 2)) with ((an ^ 2 - bn ^ 2)/(2 ^ 2)) by field.
rewrite sqrt_div_alt;[|psatzl R].
unfold Rdiv; rewrite -> sqrt_pow2, !(Rmult_comm _ (/2)), M_scal; lt0.
Qed.

Lemma M_ag_diff_squares n x : 0 < x < 1 ->
  2 ^ n * M (u_ n x) (sqrt (u_ n x ^ 2 - snd (ag 1 x n) ^ 2)) =
   ff (sqrt (1 - x ^ 2)).
Proof.
intros intx; unfold u_.
induction n.
  now unfold ag, ff, fst, snd; rewrite -> pow1, pow_O, Rmult_1_l.
replace (2 ^ S n) with (2 ^ n * 2) by (simpl; ring); rewrite Rmult_assoc.
 rewrite M_ag_diff_squares_step; psatzl R.
Qed.

Lemma Rint_ellf_sqrt_equiv :
  filterlim (fun x => RInt (ellf 1 x) 0 (sqrt x) / ln(/sqrt x))
     (at_right 0) (locally 1).
Proof.
assert (filterlim (fun x => arcsinh (/ sqrt x) / ln (/ sqrt x))
          (at_right 0) (locally 1)).
  apply (filterlim_comp _ _ _ (fun x => / sqrt x) (fun y => arcsinh y / ln y)
           _ (Rbar_locally p_infty));[ | apply ln_arcinh_equiv_infty].
  apply (filterlim_comp _ _ _ sqrt Rinv _ (at_right 0)).
    now apply filterlim_sqrt_0.
  now apply filterlim_Rinv_0_right.
apply equiv_trans with (g := fun x => arcsinh (/sqrt x)); cycle 4.
        now easy.
       now apply at_right_proper_filter.
    exists pos_half; intros y y2 y0.
    change (Rabs (y - 0) < / 2) in y2.
    assert (1 < / sqrt y).
      rewrite Rabs_right in y2; [ | psatzl R].
      rewrite <- Rinv_1, <- sqrt_1.
      now apply Rinv_lt_contravar;[ lt0 | apply sqrt_lt_1_alt; psatzl R].
    now rewrite <- arcsinh_0; apply Rgt_not_eq, arcsinh_lt; lt0.
  exists pos_half; intros y y2 y0.
  change (Rabs (y - 0) < / 2) in y2.
  assert (1 < / sqrt y).
    rewrite Rabs_right in y2; [ | psatzl R].
    rewrite <- Rinv_1, <- sqrt_1.
    now apply Rinv_lt_contravar;[ lt0 | apply sqrt_lt_1_alt; psatzl R].
  now rewrite <- ln_1; apply Rgt_not_eq, ln_increasing; lt0.
assert (help : forall x,  x * (x * 1) = x ^ 2) by (intros; ring).
assert (ctinv : continuous (fun x => / sqrt (x ^ 2 + 1)) 0).
  now apply: ex_derive_continuous; auto_derive; repeat split; lt0.
intros P [eps peps].
destruct (ctinv (ball (/sqrt (0 ^ 2 + 1)) eps)) as [delta1 Pd1].
  now exists eps; tauto.
set d0 := Rmin delta1 (Rmin ((delta1 / 2) ^ 2) 1) / 2.
assert (delta0 : 0 < d0) by now unfold d0; destruct delta1; simpl; lt0.
exists (mkposreal _ delta0).
intros x xd x0; change (ball 0 d0 x) in xd; apply peps.
assert (s0 : 0 <= sqrt x) by lt0.
assert (ris : ex_RInt (fun t => /sqrt (t ^ 2 + x ^ 2)) 0 (sqrt x)).
  apply: ex_RInt_continuous; intros z _; apply: ex_derive_continuous.
  now auto_derive; rewrite !help; repeat split; lt0.
assert (vris := int_arcsinh x x0).
assert (cmp : forall y : R,
       0 < y < sqrt x ->
       (fun t : R => / sqrt ((t ^ 2 + 1 ^ 2) * (t ^ 2 + x ^ 2))) y <=
       (fun t : R => / sqrt (t ^ 2 + x ^ 2)) y).
  intros y inty; apply Rle_Rinv;[lt0 | lt0 | ].
  apply sqrt_le_1_alt; assert (tmp := pow2_ge_0 y); rewrite pow1.
  enough (t : forall a b, 0 <= a -> 0 <= b -> b <= (a + 1) * b) by
    (apply t; auto; lt0).
  now intros; rewrite <- Rmult_1_l at 1; apply Rmult_le_compat_r; psatzl R.
assert (rib : ex_RInt
          (fun t => /sqrt (((delta1/2)^2 + 1) * (t ^ 2 + x ^ 2))) 0 (sqrt x)).
  apply:ex_RInt_continuous; intros; apply: ex_derive_continuous.
  now auto_derive; repeat split; lt0.
assert (cmp' : forall y : R,
         0 < y < sqrt x ->
        (fun t : R => / sqrt (((delta1/2) ^ 2 + 1) * (t ^ 2 + x ^ 2))) y <=
        (fun t : R => / sqrt ((t ^ 2 + 1 ^ 2) * (t ^ 2 + x ^ 2))) y).
  intros y inty; apply Rle_Rinv;[lt0 | lt0 | ].
  apply sqrt_le_1_alt, Rmult_le_compat_r;[lt0 | ].
  rewrite pow1; apply Rplus_le_compat_r, pow_incr; split; [lt0 | ].
  apply Rle_trans with (1 := Rlt_le _ _ (proj2 inty)).
  rewrite <- (sqrt_pow2 (delta1/2));[ | lt0].
  apply sqrt_le_1_alt, Rlt_le.
  revert xd; unfold ball; simpl;
     unfold AbsRing_ball, abs, minus, opp, plus; simpl.
  rewrite -> Ropp_0, Rplus_0_r, Rabs_right;[ | lt0].
  intros xd; apply Rlt_le_trans with (1 := xd).
  apply Rle_trans with ((delta1 / 2) ^ 2 / 2).
    apply Rmult_le_compat_r; try lt0.
    now apply Rle_trans with (1 := Rmin_r _ _), Rmin_l.
  now fold ((delta1 / 2) ^ 2); assert (t := pow2_ge_0 (delta1 / 2)); psatzl R.
assert (scal :
         RInt (fun t : R => / sqrt (((delta1/2) ^ 2 + 1) * (t ^ 2 + x ^ 2)))
             0 (sqrt x) = /sqrt ((delta1 / 2) ^ 2 + 1) *
             arcsinh(/ sqrt x)).
   rewrite <- (RInt_ext (fun t => / sqrt ((delta1 / 2) ^ 2 + 1) *
                                          / sqrt (t ^ 2 + x ^ 2))); cycle 1.
    now intros z _; rewrite -> sqrt_mult, Rinv_mult_distr;lt0.
  now rewrite -> RInt_scal, vris.
rewrite ball_Rabs.
assert (0 < arcsinh(/sqrt x)) by (rewrite <- arcsinh_0; apply arcsinh_lt; lt0).
rewrite <- Rabs_Ropp, -> Rabs_right, Ropp_minus_distr.
  apply Rle_lt_trans with (1 - RInt (fun t => /sqrt (((delta1 / 2) ^ 2 + 1) *
                                                (t ^ 2 + x ^ 2))) 0 (sqrt x)/
                           RInt (fun t => /sqrt (t ^ 2 + x ^ 2)) 0 (sqrt x)).
    rewrite vris.
    apply Rplus_le_compat_l, Ropp_le_contravar, Rmult_le_compat_r;[lt0 | ].
    apply RInt_le;[lt0 | auto | | exact cmp'].
    unfold ellf; apply: ex_RInt_continuous.
    now intros; apply: ex_derive_continuous; auto_derive; repeat split; lt0.
  unfold Rdiv at 1; rewrite -> scal, <- vris, Rmult_assoc, Rinv_r,
    Rmult_1_r;[ | lt0].
  pattern 1 at 1; replace 1 with (/sqrt (0 ^ 2 + 1)) by
   (rewrite -> pow_i, Rplus_0_l, sqrt_1, Rinv_1;[auto | lia]).
  assert (/sqrt ((delta1 / 2) ^ 2 + 1) <= /sqrt (0 ^ 2 + 1)).
  apply Rle_Rinv;[lt0 | lt0 | apply sqrt_le_1_alt, Rplus_le_compat_r, pow_incr].
    now destruct delta1; simpl; psatzl R.
  rewrite <- (Rabs_pos_eq (_ - _)), <- Rabs_Ropp, Ropp_minus_distr';[| psatzl R].
  apply (Pd1 (delta1 / 2)).
  now rewrite -> ball_Rabs, Rabs_right; destruct delta1; simpl; psatzl R.
apply Rle_ge, Rmult_le_reg_r with (arcsinh (/ sqrt x)); auto; rewrite Rmult_0_l.
rewrite Ropp_minus_distr.
unfold Rdiv at 1; rewrite -> Rmult_minus_distr_r, Rmult_1_l, Rmult_assoc.
rewrite -> Rinv_l, Rmult_1_r;[ | lt0].
rewrite <- vris, <- Rminus_le_0. apply RInt_le; try lt0.
apply: ex_RInt_continuous; intros; unfold ellf; apply:ex_derive_continuous.
now auto_derive; repeat split; lt0.
Qed.

Lemma M1x_at_0 : filterlim (fun x => M 1 x / (- PI / (2 * ln x)))
                  (at_right 0) (locally 1).
Proof.
assert (pi_0 := PI_RGT_0).
apply filterlim_ext_loc with
  (fun x => / (RInt (ellf 1 x) 0 (sqrt x) / ln (/ sqrt x))).
  exists pos_half; intros y y2 y0; change (Rabs (y - 0) < / 2) in y2.
  rewrite Rabs_right in y2;[ | lt0].
  replace (RInt (ellf 1 y) 0 (sqrt y)) with (/ 4 * ell 1 y); cycle 1.
    now rewrite -> quarter_elliptic; try lt0; field.
  rewrite ell_agm; try lt0.
  replace (ln (/ sqrt y)) with (-/2 * ln y); cycle 1.
    replace y with (sqrt y ^ 2) at 1 by (apply pow2_sqrt; lt0).
    now rewrite -> ln_pow, ln_Rinv;[ simpl; field | lt0 | lt0].
  unfold ff; field; repeat split; [| lt0 | apply Rgt_not_eq, M0; lt0].
  now rewrite <- ln_1; apply Rlt_not_eq, ln_increasing; lt0.
apply (filterlim_comp _ _ _ _ Rinv _ (locally 1)).
  now apply Rint_ellf_sqrt_equiv.
evar_last.
  now apply (filterlim_Rbar_inv (Finite 1)); injection; lt0.
simpl; rewrite Rinv_1; reflexivity.
Qed.

Lemma w_lt_u n x : 0 < x < 1 -> w_ n x < u_ n x.
Proof.
intros intx.
assert (help : forall u v, u ^ 2 - v ^ 2 = (u - v) * (u + v)) by (intros; ring).
assert (wp : 0 < w_ n x) by (apply w0; lt0).
assert (up : 0 < u_ n x) by (destruct (ag_le n 1 x); unfold u_; try lt0).
rewrite <- (sqrt_pow2 (u_ n x)); try lt0; unfold w_; apply sqrt_lt_1_alt.
destruct (ag_le n 1 x); try lt0.
split; try lt0.
  now rewrite help; apply Rmult_le_pos; lt0.
now assert (0 < snd (ag 1 x n) ^ 2); unfold u_; lt0.
Qed.

Lemma ln_w_div_u n x : 0 < x < 1 -> ln (w_ n x / u_ n x) < 0.
Proof.
intros intx.
assert (help : forall u v, u ^ 2 - v ^ 2 = (u - v) * (u + v)) by (intros; ring).
assert (wp : 0 < w_ n x) by (apply w0; lt0).
assert (up : 0 < u_ n x) by (destruct (ag_le n 1 x); unfold u_; try lt0).
rewrite <- ln_1; apply ln_increasing;[lt0 | ].
apply (Rmult_lt_reg_r (u_ n x));[lt0 | ]; rewrite Rmult_1_l.
unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l, Rmult_1_r;[ | lt0].
now apply w_lt_u.
Qed.

Lemma is_lim_k x : 0 < x < 1 -> is_lim_seq (fun n => k_ n x)
                ((PI/2) * ff x / ff (sqrt( 1 - x ^ 2))).
Proof.
assert (pi_0 := PI_RGT_0).
intros intx.
assert (help : forall u v, u ^ 2 - v ^ 2 = (u - v) * (u + v)) by (intros; ring).
assert (help2 : forall x, 2 * (x / 2) = x) by (intros; field).
assert (limw : is_lim_seq (fun n => w_ n x) 0).
  assert (lim_sqrt : filterlim sqrt (at_right 0) (at_right 0))
    by apply filterlim_sqrt_0.
  unfold w_; apply (filter_le_trans) with (at_right 0); cycle 1.
    unfold at_right; change (Rbar_locally 0) with (locally 0).
    now apply filter_le_within.
  apply filterlim_comp with (at_right 0); intros P [eps peps]; cycle 1.
    now apply lim_sqrt; exists eps; tauto.
  destruct (fun h => is_lim_seq_geom (/2) h (ball 0 eps)) as [N Pn].
      now rewrite Rabs_right; lt0.
    now apply locally_ball.
  exists (N + 1)%nat; intros n Nn.
  assert (0 < fst (ag 1 x n) ^ 2 - snd (ag 1 x n) ^ 2).
    rewrite help; assert (t := ag_lt n 1 x intx).
    now destruct (ag_le n 1 x); lt0.
  apply peps; auto.
  change (Rabs ((fst (ag 1 x n) ^ 2 - snd (ag 1 x n) ^ 2) - 0) < eps).
  rewrite -> Rabs_right, Rminus_0_r, help; try lt0.
  destruct n as [ | p]; try lia.
  assert (t := agm_conv 1 x (S p) Rlt_0_1 (proj1 intx)
               (Rlt_le _ _ (proj2 intx))).
  apply Rlt_trans with ((1 / 2 ^ (S p) * (2 * (fst (ag 1 x (S (S p))))))).
    replace (S (S p)) with (1 + S p)%nat by ring; rewrite ag_shift.
    simpl ag; simpl fst; rewrite help2; apply Rmult_lt_compat_r.
      destruct (ag_le p ((1 + x) / 2) (sqrt (1 * x))); try lt0.
        now destruct (ag_le 1 1 x); simpl in *; lt0.
      now assert (0 < sqrt (1 * x)); lt0.
    apply Rle_lt_trans with ((1 - x) / 2 ^ S p).
      now apply (agm_conv 1 x (S p)); lt0.
    now apply Rmult_lt_compat_r; lt0.
  apply Rlt_trans with (1 / 2 ^ (S p) * (2 * 1)).
    repeat apply Rmult_lt_compat_l; try lt0.
    replace (S (S p)) with (S p + 1)%nat by ring; rewrite ag_shift.
    simpl (fst (ag 1 x 1)); simpl (snd (ag 1 x 1)).
    destruct (ag_le (S p) ((1 + x) /2) (sqrt (1 * x))); try lt0.
    now destruct (ag_le 1 1 x); simpl in *; lt0.
  replace (1 / 2 ^ S p * (2 * 1)) with (/ 2 ^ p) by (simpl; field; lt0).
  assert (Np : (N <= p)%nat) by lia.
  rewrite <- (Rabs_right (/ _)), <- (Rminus_0_r (/ _)); try lt0.
    rewrite Rinv_pow; try lt0; apply Pn; lia.
  now apply Rle_ge, Rlt_le; lt0.
assert (fp : forall n, 0 < w_ n x / u_ n x).
  intros n; assert (tw := w0 n x intx).
  now destruct (ag_le n 1 x Rlt_0_1); unfold u_; lt0.
assert (limwu : filterlim (fun n => w_ n x / u_ n x) Hierarchy.eventually
          (Rbar_locally 0)).
  apply (is_lim_seq_div _ _ 0 (ff x)); auto.
      now apply is_lim_seq_M; lt0.
    now injection; apply Rgt_not_eq, M0; lt0.
  now unfold is_Rbar_div, is_Rbar_mult; simpl; rewrite Rmult_0_l.
apply is_lim_seq_ext with
 (fun n => (ff (w_ n x / u_ n x)  / (-PI/(2 * ln (w_ n x / u_ n x))) *
           (/(ff (w_ n x / u_ n x) * ((- /((PI/ 2) / ln (w_ n x / u_ n x)))))
                          * k_ n x))).
  intros; field.
  assert (wp : 0 < w_ n x) by (apply w0; lt0).
  assert (up : 0 < u_ n x) by (destruct (ag_le n 1 x); unfold u_; try lt0).
  assert (t:= ln_w_div_u n x intx); unfold ff.
  now split;[apply Rlt_not_eq; lt0| split;[lt0 |apply Rgt_not_eq, M0; lt0]].
apply: (is_lim_seq_mult _ _ 1 (PI/2 * ff x / ff(sqrt (1 - x ^ 2)))); cycle 2.
    now unfold is_Rbar_mult; cbn -[pow]; rewrite Rmult_1_l.
  apply (filterlim_comp _ _ _ (fun n => (w_ n x / u_ n x))
             (fun y => ff y / (- PI/(2 * ln y))) _ (at_right 0)).
    intros P [eps Peps].
    destruct (limwu (ball 0 eps) (locally_ball _ _)) as [bound pb].
    now exists bound; intros n Pn; apply Peps; auto.
  exact M1x_at_0.
apply is_lim_seq_ext with
   (fun n => (PI / 2) * / (2 ^ n * ff (w_ n x / u_ n x))).
  intros n; unfold k_.
  assert (wp : 0 < w_ n x) by (apply w0; lt0).
  assert (up : 0 < u_ n x) by (destruct (ag_le n 1 x); unfold u_; lt0).
  replace (ln (u_ n x / w_ n x)) with (- ln (w_ n x / u_ n x)) by
   (rewrite <- ln_Rinv;[apply f_equal; field| ]; try lt0).
  field; repeat split; try lt0.
    now apply Rlt_not_eq, ln_w_div_u.
  now unfold ff; apply Rgt_not_eq, M0; auto; psatzl R.

assert (ff1m : 0 < ff (sqrt (1 - x ^ 2))).
  now apply M0; try lt0; replace (1 - x ^ 2) with ((1 - x) * (1 + x)); lt0.
assert (ffx : 0 < ff x).
  now apply M0; lt0.
apply (is_lim_seq_mult _ _ (PI/2) (ff x / ff(sqrt(1 - x ^ 2)))); cycle 2.
    unfold is_Rbar_mult; simpl; apply f_equal, f_equal; field.
    now apply Rgt_not_eq; exact ff1m.
  now apply is_lim_seq_const.
replace (ff x / ff (sqrt (1 - x ^ 2))) with
  (/ (ff (sqrt (1 - x ^ 2)) / ff x));[ | field; lt0].
apply (filterlim_comp _ R R _ Rinv _
         (locally (ff (sqrt (1 - x ^ 2)) / ff x))); cycle 1.
  apply: (filterlim_Rbar_inv (ff (sqrt (1 - x ^ 2)) / ff x)).
  injection; apply Rgt_not_eq, Rmult_lt_0_compat.
    exact ff1m.
  now lt0.
apply filterlim_ext with (fun n => ff (sqrt (1 - x ^ 2)) / u_ n x).
  intros n; rewrite <- (M_ag_diff_squares n); try lt0; unfold Rdiv at 1.
  assert (wp : 0 < w_ n x) by (apply w0; lt0).
  assert (up : 0 < u_ n x) by (destruct (ag_le n 1 x); unfold u_; lt0).
  rewrite -> Rmult_assoc, <- (Rmult_comm (/ u_ n x)), <- M_scal; try lt0.
  now rewrite Rinv_l; try lt0; rewrite (Rmult_comm (/ u_ _ _)).
apply (filterlim_comp _ R R (fun n => u_ n x) (fun y => ff (sqrt (1 - x ^ 2)) / y)
         _ (locally (ff x))).
  now apply (is_lim_seq_M 1 x); lt0.
change (continuous (fun y => ff (sqrt (1 - x ^ 2)) / y) (ff x)).
apply (continuous_mult (fun _ => ff (sqrt (1 - x ^ 2)))
             (fun y => / y)).
  now apply continuous_const.
unfold continuous.
  apply (filterlim_Rbar_inv (ff x)); injection; lt0.
Qed.

Lemma CVU_derive_k_n :
  forall lb ub, 0 < lb < ub -> ub < 1 -> forall c delta,
   (forall y, Boule c delta y -> lb < y < ub) ->
   CVU (fun n x => Derive (k_ n) x) (fun x => ff x ^ 2/(x * (1 - x ^ 2))) c delta.
intros lb ub [ub0 ul] lb1 x delta Pb.
assert (ctpoly : forall y, lb <= y <= ub ->
           continuity_pt (fun z => z * (1 - z ^ 2)) y) by (intros; reg).
destruct (continuity_ab_min
            (fun x => x * (1 - x ^ 2)) lb ub (Rlt_le _ _ ul) ctpoly) as
 [bot [pbot inbounds]]; clear ctpoly.
assert (0 < bot * (1 - bot ^ 2)).
  now replace (1 - bot ^ 2) with ((1 + bot) * (1 - bot)) by ring; lt0.
assert (bnd : forall y n, 0 < y < 1 -> u_ n y - snd(ag 1 y n) <= 1 / 2 ^ n).
  intros y [ | n] inty.
    now unfold u_; simpl; psatzl R.
  apply Rle_trans with ((1 - y) / 2 ^ S n).
    now apply (agm_conv 1 y (S n)); lt0.
  now apply Rmult_le_compat_r; lt0.
intros eps ep.
assert (dpos : 0 < eps * (bot * (1 - bot ^ 2))) by lt0.
destruct (cv_div2 1 (ball 0 (mkposreal _ dpos))) as [N Pn].
  now apply locally_ball.
exists (N + 1)%nat; intros n y nN dyx.
assert (nN' : (n >= N)%nat) by lia.
apply Pb in dyx.
(* bug: why do I have to clear the context here? *)
assert (inty : 0 < y < 1) by (clear -dyx ub0 ul lb1; psatzl R).
rewrite Derive_k;[ | psatzl R].
assert (t : forall a b c, a/c - b/c = (a-b)/c) by (intros; unfold Rdiv; ring).
rewrite -> t, Rabs_pos_eq; clear t.
  apply Rle_lt_trans with ((ff y ^ 2 - snd (ag 1 y n) ^ 2)/(bot *(1- bot^ 2))).
    apply Rmult_le_compat_l.
      destruct (bound_modulus_convergence_snd_ag n y); try psatzl R.
      destruct (ag_le n 1 y); try lt0.
      now rewrite <- Rminus_le_0; apply pow_incr; split; psatzl R.
    assert (bot * (1 - bot ^ 2) <= y * (1 - y ^ 2)).
      now apply pbot; psatzl R.
    now apply Rle_Rinv; psatzl R.
  destruct (bound_modulus_convergence_snd_ag n y) as [c1 c2]; try psatzl R.
  apply Rmult_lt_reg_r with (bot * (1 - bot ^ 2));[lt0 | ].
  unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l, Rmult_1_r;[|lt0].
  replace (ff y ^ 2 - snd (ag 1 y n) ^ 2) with
      ((ff y + snd (ag 1 y n)) * (ff y - snd (ag 1 y n))) by ring.
  destruct n as [ | n];[elimtype False; clear -nN; lia | ].
  assert (nN2 : (n >= N)%nat) by lia.
  assert (Pn' := Pn n nN2); revert Pn'; rewrite ball_Rabs.
  rewrite -> Rminus_0_r, Rabs_right; try (apply Rle_ge; lt0).
  simpl; intros Pn'.
  apply Rle_lt_trans with (2 * (ff y - snd (ag 1 y (S n)))).
    apply Rmult_le_compat_r;[psatzl R | ].
    assert (ff y <= 1).
      assert (t := dist_u_ff 1 y (le_n _) (proj1 inty)).
      rewrite Rabs_right in t;[ | psatzl R].
      now unfold u_ in t; simpl in t; rewrite Rmult_1_r in t; psatzl R.
    now simpl in c1; psatzl R.
  replace (eps * (bot * (1 - bot * (bot * 1)))) with
         (2 * ((eps * (bot * (1 - bot ^ 2)))/2))
   by field.
  apply Rmult_lt_compat_l;[lt0 | ].
  apply Rle_lt_trans with (1 := c2).
  replace (Rabs (1 - y) / 2 ^ S n) with ((Rabs (1 - y)/2 ^n) / 2) by
  (simpl; field; lt0).
  apply Rmult_lt_compat_r;[lt0 | ].
  apply Rle_lt_trans with (2 := Pn'), Rmult_le_compat_r;[lt0 |].
  now rewrite Rabs_right; psatzl R.
apply Rmult_le_pos.
  destruct (bound_modulus_convergence_snd_ag n y) as [c1 c2]; try psatzl R.
  replace (ff y ^ 2 - snd (ag 1 y n) ^ 2) with
     ((ff y + snd (ag 1 y n)) * (ff y - snd (ag 1 y n))) by ring.
  destruct (ag_le n 1 y); try psatzl R.
  now apply Rmult_le_pos; psatzl R.
assert (bot * (1 - bot ^ 2) <= y * (1 - y ^ 2)) by (apply pbot; psatzl R); lt0.
Qed.

Lemma main_derivative_formula : forall x, 0 < x < 1 ->
  is_derive (fun x => (PI/2) * ff x / ff (sqrt (1 - x ^ 2))) x
       (ff x ^ 2/(x * (1 - x ^ 2))).
Proof.
intros x intx.
assert (d0 : 0 < Rmin (x / 2) ((1 - x) / 2)) by (apply Rmin_glb_lt; lt0).
set (delta := mkposreal _ d0).
assert (delta <= (x / 2)) by apply Rmin_l.
assert (delta <= (1 - x) / 2) by apply Rmin_r.
assert (dern :
          forall y n, Boule x delta y ->
          is_derive (k_ n) y (Derive (k_ n) y)).
  intros y n dyx; unfold Boule in dyx; apply Rabs_lt_between in dyx.
  now apply Derive_correct; eapply ex_intro; apply is_derive_k; lt0.
assert (dern' :
          forall n y, Boule x delta y ->
          derivable_pt_lim (k_ n) y (Derive (k_ n) y)).
  now intros n y boy; rewrite <- is_derive_Reals; apply dern; auto.
assert (cv_k_n : forall y : R,
       Boule x delta y ->
       Un_cv (fun n : nat => k_ n y)
         ((fun x : R => PI / 2 * ff x / ff (sqrt (1 - x ^ 2))) y)).
  intros y dyx; unfold Boule in dyx; apply Rabs_lt_between in dyx.
  rewrite <- is_lim_seq_Reals; apply is_lim_k; lt0.
assert (cvu_dk_n : CVU (fun n x => Derive (k_ n) x)
          (fun x => ff x ^ 2 / (x * (1 - x ^ 2))) x delta).
  apply (CVU_derive_k_n (x - delta) (x + delta));
  [assert (tmp := cond_pos delta); psatzl R | psatzl R | ].
  now intros y dy; unfold Boule in dy; apply Rabs_lt_between in dy; psatzl R.
rewrite is_derive_Reals.
apply (CVU_derivable _ _ _ _ x delta cvu_dk_n cv_k_n dern' x (Boule_center _ _)).
Qed.

Lemma PI_from_ff_ff' :
   PI = 2 * sqrt 2 * ff (/ sqrt 2) ^ 3 / Derive ff (/ sqrt 2).
Proof.
assert (help : forall y, 1 - y ^ 2 = (1 + y) * (1 - y)) by (intros; ring).
assert (help' : forall y, y * (y * 1) = y ^ 2) by (intros; ring).
assert (help2 : forall a b c, c <> 0 -> a = (b / 2) * c -> b = 2 * a / c).
  now intros a b c c0 q; rewrite q; field.
assert (vs2 : (/ sqrt 2) ^ 2 = / 2) by (rewrite <- Rinv_pow, sqrt_pow_2; lt0).
assert (md : 1 - /2 = / 2) by field.
assert (ts : 2 * / sqrt 2 = sqrt 2).
  now rewrite <- (pow2_sqrt 2) at 1;[field | ]; lt0.
assert (vs : sqrt (/2) = / sqrt 2) by now  rewrite inv_sqrt; lt0.
assert (main : forall x, 0 < x < 1 ->
           is_derive (fun x => PI/2 * ff x / ff (sqrt (1 - x ^ 2))) x
           (PI/2 * ((Derive ff x * ff (sqrt (1 - x ^ 2)) +
                (Derive ff (sqrt (1 - x ^ 2))  *
                  (/(2 * sqrt (1 - x ^ 2)) * (2 * x))) * ff x)/
                   ff (sqrt (1 - x ^ 2)) ^ 2))).
  intros x intx.
  assert (0 < 1 - x ^ 2) by (rewrite help; lt0).
  assert (1 - x ^ 2 < 1)
    by (assert (t' := pow_lt x 2 (proj1 intx)); psatzl R).
  assert (sqrt (1 - x ^ 2) < 1).
    now rewrite <- sqrt_1 at 2; apply sqrt_lt_1_alt; lt0.
  assert (0 < sqrt (1 - x ^ 2)) by lt0.
  assert (ff (sqrt (1 - x ^ 2)) <> 0).
    now unfold ff; destruct (Mbounds 1 (sqrt (1 - x ^ 2))); lt0.
  apply (is_derive_ext (fun x => PI/2 * (ff x /ff(sqrt(1-x^2)))));
    [simpl; intros y; unfold Rdiv; ring | ].
  auto_derive; rewrite help'; change (1 + - x ^ 2) with (1 - x ^ 2).
    now repeat (split;[ apply ex_derive_ff; try lt0 | ]); auto.
  now change (fun x => ff x) with ff; field; split; lt0.
assert (main2 := main _ ints); apply is_derive_unique in main2; clear main.
rewrite (is_derive_unique _ _ _ (main_derivative_formula _ ints)) in main2.
assert (0 < Derive ff (/sqrt 2)) by (apply derive_ff_pos; auto using ints).
assert (0 < ff (/ sqrt 2)) by (apply (M0 1 (/sqrt 2)); lt0).
apply help2 in main2; cycle 1.
  now repeat (rewrite -> vs2 || rewrite md || rewrite ts || rewrite vs); lt0.
rewrite main2.
now repeat(rewrite -> ?vs2, ?md, ?ts, ?vs); field; repeat split; lt0.
Qed.

Lemma is_lim_seq_fst_ag x : 0 < x < 1 ->
  is_lim_seq (fun n => fst (ag 1 x n)) (ff x).
Proof.
intros intx P [eps peps]; assert (mx0 : 0 < 1 - x) by lt0.
destruct (cv_div2 (1 - x) (ball 0 eps) (locally_ball _ _)) as [N pn].
exists N; intros n nn; apply peps; rewrite ball_Rabs.
unfold ff; rewrite <- (M_shift 1 x n); try lt0.
destruct (ag_le n 1 x); try lt0.
destruct (Mbounds (fst (ag 1 x n)) (snd (ag 1 x n))); try lt0.
assert (t := agm_conv 1 x n Rlt_0_1 (proj1 intx) (Rlt_le _ _ (proj2 intx))).
apply Rle_lt_trans with (Rabs ((1 - x) / 2 ^ n - 0)); cycle 1.
  now apply pn.
rewrite -> !Rabs_right, Rminus_0_r; try lt0.
Qed.

Lemma is_lim_seq_snd_ag x : 0 < x < 1 ->
  is_lim_seq (fun n => snd (ag 1 x n)) (ff x).
Proof.
intros intx P [eps peps]; assert (mx0 : 0 < 1 - x) by lt0.
destruct (cv_div2 (1 - x) (ball 0 eps) (locally_ball _ _)) as [N pn].
exists N; intros n nn; apply peps; apply ball_sym; rewrite ball_Rabs.
unfold ff; rewrite <- (M_shift 1 x n); try lt0.
destruct (ag_le n 1 x); try lt0.
destruct (Mbounds (fst (ag 1 x n)) (snd (ag 1 x n))); try lt0.
assert (t := agm_conv 1 x n Rlt_0_1 (proj1 intx) (Rlt_le _ _ (proj2 intx))).
apply Rle_lt_trans with (Rabs ((1 - x) / 2 ^ n - 0)); cycle 1.
  now apply pn.
rewrite -> !Rabs_right, Rminus_0_r; try lt0.
Qed.

Lemma cv_ff_3_over_ff' :
  is_lim_seq (fun n => snd (ag 1 (/sqrt 2) n) ^ 2 * u_ n (/sqrt 2) /
                         Derive (u_ n) (/sqrt 2)) (PI / (2 * sqrt 2)).
Proof.
assert (pi_0 := PI_RGT_0).
assert (ints2 : 0 < /sqrt 2 < 1) by exact ints.
assert (dfs := derive_ff_pos _ ints2).
replace (PI / (2 * sqrt 2)) with
  (ff (/sqrt 2) ^ 3 / Derive ff (/sqrt 2)); cycle 1.
  now rewrite PI_from_ff_ff'; field; split; lt0.
apply is_lim_seq_mult with (ff (/sqrt 2) ^ 3) (/ Derive ff (/sqrt 2)); cycle 2.
    unfold is_Rbar_mult; cbn [Rbar_mult']; apply f_equal, f_equal.
    now unfold Rdiv; ring.
  apply is_lim_seq_mult with (ff (/sqrt 2) ^ 2) (ff (/sqrt 2)); cycle 2.
      unfold is_Rbar_mult; cbn [Rbar_mult']; apply f_equal, f_equal; ring.
    apply: (is_lim_seq_continuous  (fun x => x ^ 2)).
      now reg.
    now apply is_lim_seq_snd_ag.
  now apply is_lim_seq_fst_ag.
apply (is_lim_seq_continuous Rinv); [reg; lt0 | ].
assert (0 < (/sqrt 2) / 2) by psatzl R.
assert (halfsint : 0 < (/sqrt 2) / 2 < 1) by psatzl R.
assert (d0 : 0 < (1 - (/sqrt 2) / 2) / 2) by psatzl R.
assert (tmp := cv_u_ff' _ (mkposreal _ d0) halfsint (refl_equal _)).
rewrite is_lim_seq_Reals.
apply (CVU_cv (fun n => Derive (u_ n)) (Derive ff)
                 ((/sqrt 2 / 2 + 1) / 2) (mkposreal _ d0)); auto.
unfold Boule; apply Rabs_def1; simpl; psatzl R.
Qed.

Fixpoint agmpi n :=
  match n with
    0%nat => (2 + sqrt 2)
  | S p => agmpi p * (1 + y_ n (/sqrt 2)) / (1 + z_ n (/sqrt 2))
  end.

Lemma agmpi_step n :
  agmpi n = match n with
    0%nat => (2 + sqrt 2)
  | S p => agmpi p * (1 + y_ n (/sqrt 2)) / (1 + z_ n (/sqrt 2))
  end.
Proof. destruct n as [ | p]; reflexivity. Qed.

Lemma agmpi0 : agmpi 0 =
   2 * sqrt 2 * (snd (ag 1 (/sqrt 2) 1) ^ 2 * fst (ag 1 (/sqrt 2) 1)  /
                 Derive (fun x => fst (ag 1 x 1)) (/sqrt 2)).
Proof.
assert (dag1 : Derive (fun x => (1 + x) / 2) (/sqrt 2) = / 2).
  now apply is_derive_unique; auto_derive; auto; field.
rewrite ag_step; unfold ag, fst, snd; rewrite sqrt_pow_2; [ | lt0].
rewrite dag1; simpl; set (u := sqrt 2).
replace 2 with (u ^ 2) by (unfold u; rewrite pow2_sqrt; lt0).
field; unfold u; lt0.
Qed.

Lemma cv_agmpi : is_lim_seq agmpi PI.
Proof.
assert (ints : 0 < /sqrt 2 < 1) by exact ints.
assert (le1s : forall n, (1 <= S n)%nat) by (intros; lia).
apply (is_lim_seq_ext (fun n => 2 * sqrt 2 *
                ((snd (ag 1 (/sqrt 2) (n + 1)) ^ 2 * u_ (n + 1) (/sqrt 2))
                  / Derive (u_ (n + 1)) (/sqrt 2)))).
  induction n as [ | n IHn].
    simpl Peano.plus; rewrite agmpi0; unfold u_; reflexivity.
  simpl (Peano.plus); rewrite agmpi_step.
  assert (t := ag_le (S n) 1 (/sqrt 2) Rlt_0_1 (proj1 ints)
            (Rlt_le _ _ (proj2 ints))).
  assert (t' := compare_derive_ag (S n) (/sqrt 2) (le1s _) ints).
  assert (t'' := compare_derive_ag (S (S n)) (/sqrt 2) (le1s _) ints).
  unfold Rdiv; rewrite -> ratio_z, ratio_y, <- IHn, !Rmult_assoc; auto; try lia.
  replace (S n + 1)%nat with (S (S n)) by ring; unfold u_ in t, t', t'' |- *.
  replace (n + 1)%nat with (S n) by ring.
  field; try lt0.
apply (is_lim_seq_subseq
         (fun n => 2 * sqrt 2 *
              (snd (ag 1 (/sqrt 2) n) ^ 2 * u_ n (/sqrt 2)
              / Derive (u_ n) (/sqrt 2))) PI (fun x : nat => (x + 1)%nat)).
  now apply eventually_subseq_loc, filter_forall; intros; lia.
replace PI with ((2 * sqrt 2) * (PI/(2 * sqrt 2))) by (field; lt0).
apply is_lim_seq_mult with (2 * sqrt 2) (PI / (2 * sqrt 2));
  [apply is_lim_seq_const | | easy].
now apply cv_ff_3_over_ff'.
Qed.

Lemma over_ystep : forall x, 1 < x -> yfun x <= 1 + (x - 1)^2/8.
Proof.
assert (sqrt3 : forall x, 0 < x -> sqrt x ^ 3 = x * sqrt x).
  intros x x0; replace (sqrt x ^ 3) with (sqrt x ^ 2 * sqrt x) by ring.
  now rewrite pow2_sqrt; lt0.
assert (d1 : forall x, 0 < x -> is_derive yfun x ((x - 1)/(4 * (sqrt x) ^ 3))).
  intros; unfold yfun; auto_derive;[repeat split; auto; lt0 |].
  now field_simplify; try lt0; rewrite sqrt_pow_2; lt0.
assert (d2 : forall x, 0 < x ->
           is_derive (fun y => (y - 1) / (4 * sqrt y ^ 3)) x
           ((3 - x) / (8 * sqrt x ^ 5))).
  intros x x0; auto_derive.
    now repeat split; lt0.
  set (u := sqrt x); rewrite <- (sqrt_pow_2 x); try lt0; fold u; field.
  now unfold u; lt0.
intros x x1.
assert (tx0 : 0 < 2 * x) by psatzl R.
assert (d1' : forall y, 0 < y < 2 * x ->
              is_derive yfun y ((y - 1)/(4 * sqrt y ^ 3))).
  now intros y iny; apply d1; lt0.
assert (d2' : forall y, 0 < y < 2 * x ->
              is_derive (fun y => ((y - 1)/(4 * sqrt y ^ 3))) y
                 ((3 - y) / (8 * sqrt y ^ 5))).
  now intros y iny; apply d2; psatzl R.
assert (int1 : 0 < 1 < x) by psatzl R.
assert (x2x : x < 2 * x) by psatzl R.
destruct (small_taylor_lagrange2 yfun
              (fun y => (y - 1)/(4 * sqrt y ^ 3))
              (fun y => (3 - y)/(8 * sqrt y ^ 5)) 0 (2 * x) tx0 d1' d2' 1 x
              int1 x2x) as [zeta [inzeta qq]].
assert (fy1 : yfun 1 = 1) by (unfold yfun; rewrite sqrt_1; field).
fold (yfun x); rewrite -> qq, Rminus_eq_0; unfold Rdiv at 1; rewrite !Rmult_0_l.
rewrite -> Rplus_0_r, fy1; apply Rplus_le_compat_l; unfold Rdiv.
repeat (rewrite (Rmult_comm ((x - 1) ^ 2)) || rewrite Rmult_assoc).
rewrite <-!Rmult_assoc; apply Rmult_le_compat_r.
  now apply pow2_ge_0.
apply Rle_trans with ((3 - 1)/(4 * 2 * sqrt 1 ^ 5) * / 2).
  destruct (Rle_dec 0 (3 - zeta)).
    apply Rmult_le_compat; try lt0.
    now apply Rmult_le_pos; try lt0.
    apply Rmult_le_compat; try lt0.
    apply Rle_Rinv; try lt0.
    apply Rmult_le_compat_l; try lt0.
    now apply pow_incr; split;[rewrite sqrt_1 | apply sqrt_le_1_alt]; psatzl R.
  apply Rle_trans with 0.
    now repeat (apply Rmult_le_0_r; try lt0).
  now rewrite sqrt_1; ring_simplify; lt0.
now rewrite sqrt_1; field_simplify; lt0.
Qed.

Lemma majoration_y_n_plus_one n a :
  0 < a < 1 -> 0 <= y_ (n + 1) a - 1 <= (y_ n a - 1) ^ 2 / 8.
Proof.
intros inta; split.
  replace 0 with (1 - 1) by ring; unfold Rminus; apply Rplus_le_compat_r.
  apply Rlt_le; apply y_gt_1; assumption.
rewrite y_step; unfold yfun;[ | assumption].
rewrite <- (Rplus_0_r ((y_ n a - 1) ^ 2 / 8)), <-(Rminus_eq_0 1); unfold Rminus.
rewrite <- Rplus_assoc; apply Rplus_le_compat_r.
rewrite (Rplus_comm ((y_ n a + -1) ^ 2/8) 1).
apply over_ystep, y_gt_1; assumption.
Qed.

Lemma majoration_y_n n a : 0 < a < 1 ->
  0 <= y_ (n + 1) a - 1 <=
        Rpower (y_ 1 a - 1) (2 ^ n) / (Rpower 8 (2 ^ n - 1)).
Proof.
intros ina; induction n as [ | n IH].
  assert (t := y_gt_1 a 1 ina).
  now rewrite -> pow_O, Rpower_1, Rminus_eq_0, Rpower_O, plus_0_l; psatzl R.
split;[assert (t := y_gt_1 a (S n + 1) ina); psatzl R | ].
replace (S n + 1)%nat with ((n + 1) + 1)%nat by ring.
apply Rle_trans with ((y_ (n + 1) a - 1)^2/8);
  [ apply majoration_y_n_plus_one; assumption | ].
assert (help : forall a, a = (a * 8) / 8) by (intros; field).
pattern (Rpower (y_ 1 a - 1) (2 ^ S n) / Rpower 8 (2 ^ S n - 1)).
rewrite -> help; clear help; apply Rmult_le_compat_r;[lt0 | ].
apply Rle_trans with ((Rpower (y_ 1 a - 1)(2 ^ n) / Rpower 8 (2 ^ n - 1)) ^ 2).
  now apply pow_incr; auto.
apply Req_le.
replace ((Rpower (y_ 1 a - 1) (2 ^ n) / Rpower 8 (2 ^ n - 1)) ^ 2) with
  ((Rpower (y_ 1 a - 1) (2 ^ n)) ^ 2 / (Rpower 8 (2 ^ n - 1)) ^ 2) by
  (field; apply Rgt_not_eq; unfold Rpower; apply exp_pos).
rewrite <- !(Rpower_pow 2); simpl (INR 2); try psatzl R; try apply exp_pos.
rewrite -> Rpower_mult, (Rmult_comm (2 ^ n) 2).
unfold Rdiv; rewrite Rmult_assoc; apply (f_equal (Rmult _)).
rewrite -> Rpower_mult, Rmult_minus_distr_r, Rmult_1_l.
replace (2 ^ n * 2 - 2) with ((2 ^ S n - 1) - 1) by (simpl; ring).
unfold Rminus; rewrite -> Rpower_plus, Rpower_Ropp, Rpower_1; try lt0; field.
now apply Rgt_not_eq, exp_pos.
Qed.

Lemma majoration_y_n' n a : 0 < a < 1 ->
  0 <= y_ (n + 1) a - 1 <=
        8 * Rpower ((y_ 1 a - 1) / 8) (2 ^ n).
Proof.
intros inta; destruct (majoration_y_n n a inta) as [y0 yb].
split;[apply y0 | apply Rle_trans with (1 := yb), Req_le ].
assert (t := y_gt_1 a 1 inta).
unfold Rdiv; rewrite <- (Rpower_mult_distr _ _ (2 ^ n)); unfold Rminus; try lt0.
rewrite -> Rpower_plus, Rpower_Ropp, Rpower_1, Rpower_Rinv; try lt0.
field; apply Rgt_not_eq, exp_pos.
Qed.

Lemma ineq2 : (1 + ((1 + sqrt 2)/(2 * sqrt (sqrt 2))))/
              (1 + / sqrt (/ sqrt 2)) < 1.
Proof. interval. Qed.

Lemma y_0 : y_ 0 (/sqrt 2) = sqrt 2.
Proof. unfold y_, u_; simpl. field. lt0. Qed.

Lemma agm0 n : 0 < agmpi n.
Proof.
induction n as [ | n IH];[simpl; lt0 | ].
simpl; apply Rmult_lt_0_compat.
 apply Rmult_lt_0_compat;[assumption | ].
 assert (t := y_gt_1 (/sqrt 2) (S n) ints); psatzl R.
assert (Sn1 : (1 <= S n)%nat) by lia.
assert (t' := z_gt_1 (/sqrt 2) (S n) ints Sn1).
apply Rinv_0_lt_compat; psatzl R.
Qed.

Lemma agmpi_1_0 : agmpi 1 < agmpi 0.
Proof.
rewrite -> agmpi_step, z_1; try apply ints.
replace (S 0) with (0 + 1)%nat by ring; rewrite -> y_step, y_0; try apply ints.
pattern (agmpi 0) at 2; rewrite <- Rmult_1_r.
unfold Rdiv; rewrite Rmult_assoc; apply Rmult_lt_compat_l.
  apply agm0.
exact ineq2.
Qed.

Lemma majoration_y_n_vs2 n :
  0 <= y_ (n + 1) (/sqrt 2) - 1 <= 8 * Rpower 531 (- (2 ^ n)).
Proof.
destruct (majoration_y_n' n _ ints) as [t1 t2]; split; [ psatzl R | ].
apply Rle_trans with (1 := t2); clear t1 t2.
apply Rmult_le_compat_l; [lt0 | ].
replace 1%nat with (0 + 1)%nat by ring; rewrite -> y_step, y_0;[|exact ints].
rewrite -> Rpower_Ropp, <- Rpower_Rinv;[ | psatzl R].
apply Rle_Rpower_l;[apply pow_le; psatzl R | unfold yfun; split; interval].
Qed.

Lemma s_to_sum s n p :
  sum_f_R0 (fun i => s (n + i)%nat - s (n + i + 1)%nat) p =
      s n - s (n + p + 1)%nat.
Proof.
induction p as [ | p IH].
 now simpl; rewrite plus_0_r.
simpl; rewrite IH; replace (n + S p + 1)%nat with (n + p + 2)%nat by ring.
replace (n + S p)%nat with (n + p + 1)%nat by ring.
ring.
Qed.

Lemma sequence_to_series :
  forall s (l : R), is_lim_seq s l ->
  forall n, is_lim_seq (sum_f_R0 (fun i => s (n + i)%nat - s (n + i + 1)%nat))
     (s n - l).
Proof.
intros s l cv n; apply (is_lim_seq_ext (fun i => s n - s (n + i + 1)%nat)).
  now intros m; symmetry; apply s_to_sum.
apply is_lim_seq_minus with (s n) l;[ | | easy].
  apply is_lim_seq_const.
apply (is_lim_seq_ext (fun i => s (i + (n + 1))%nat)).
  now intros m; replace (m + (n + 1))%nat with (n + m + 1)%nat by ring.
now rewrite <- (is_lim_seq_incr_n s (n + 1)).
Qed.

Lemma bound_agmpi n : (1 <= n)%nat ->
  0 <= agmpi (n + 1) - PI <= 4 * agmpi 0 * Rpower 531 (- 2 ^ n).
Proof.
intros n1; assert (n2 : (1 <= n + 1)%nat) by lia.
assert (ydecr : forall p, (1 <= p)%nat -> y_(S p) (/sqrt 2) <= y_ p (/sqrt 2)).
  intros p p1; destruct (chain_y_z_y (/sqrt 2) p ints p1).
  assert (y0 := y_gt_1 _ p ints).
  assert (t : sqrt (y_ p (/sqrt 2)) <= y_ p (/sqrt 2)).
    now apply Rlt_le, gt1_imp_sqrt_lt.
  now replace (S p) with (p + 1)%nat by ring; psatzl R.
assert (step1:
 forall p, (1 <= p)%nat -> 0 <= agmpi p - agmpi (S p) <=
                agmpi p / 2 * (y_ p (/sqrt 2) - y_(S p) (/sqrt 2))).
  intros p p1; simpl; replace (S p) with (p + 1)%nat by ring.
  assert (sp1 : (1 <= p + 1)%nat) by lia.
  destruct (chain_y_z_y (/sqrt 2) p ints p1) as [yltz zltsy].
  assert (zp := z_gt_1 _ _ ints sp1).
  assert (help1 : forall a b c, c <> 0 -> a - b/c = (a * c - b)/c) by
  (intros; field; auto).
  rewrite -> help1, <- Rmult_minus_distr_l;[| psatzl R].
  assert (help2 : forall a b, (1 + a - (1 + b)) = a - b) by (intros; ring).
  rewrite help2.
  split;[repeat apply Rmult_le_pos | ]; try lt0.
    now apply Rlt_le, agm0.
  unfold Rdiv; rewrite !Rmult_assoc; apply Rmult_le_compat_l.
    now apply Rlt_le, agm0.
  rewrite Rmult_comm.
  apply Rmult_le_compat;[| |apply Rle_Rinv | apply Rplus_le_compat_r]; try lt0.
  now apply Rle_trans with (1 := zltsy), Rlt_le, gt1_imp_sqrt_lt, y_gt_1, ints.
assert (agmpi_decr : forall n m, (m <= n)%nat -> (1 <= m)%nat ->
          agmpi n <= agmpi m).
  intros p p1 h; induction h as [ | p p1p IH]; intros pp1;[apply Rle_refl |].
  now apply Rle_trans with (2 := (IH pp1)); destruct (step1 p);try lia; lt0.
assert (t := sequence_to_series agmpi PI cv_agmpi).
assert (cvy : is_lim_seq (fun n => y_ n (/sqrt 2)) 1).
  apply is_lim_seq_Reals.
  assert (0 < /2 < 1 /\ 0 < / 4) as [i2 d0] by psatzl R.
  set (d := mkposreal _ d0).
  assert (d1 : d = (1 - /2) / 2 :> R) by (simpl; psatzl R).
  assert (t' := CVU_y _ i2 d d1).
  apply (CVU_cv y_ (fun _ => 1) ((/2 + 1) / 2) d t').
  now apply Rabs_def1; simpl; interval.
assert (cvy' :
          is_lim_seq (fun p => agmpi (n + 1) / 2 * (y_ p (/sqrt 2)))
               (agmpi (n + 1) / 2)).
  apply is_lim_seq_mult with (agmpi (n + 1) / 2) 1; auto.
    now apply is_lim_seq_const.
  now unfold is_Rbar_mult, Rbar_mult'; rewrite Rmult_1_r.
assert (t' := sequence_to_series _ _ cvy'); lazy beta in t'.
assert (step2 :agmpi (n + 1) - PI <=
              agmpi (n + 1) / 2 * (y_ (n + 1) (/sqrt 2) - 1)).
  rewrite -> Rmult_minus_distr_l, Rmult_1_r.
  apply (fun h => is_lim_seq_le _ _ _ _ h (t (n + 1)%nat) (t' (n + 1)%nat)).
  assert (cmp : forall p,
  sum_f_R0 (fun i => agmpi ((n + 1) + i) - agmpi ((n + 1) + i + 1)) p <=
  sum_f_R0 (fun i => agmpi (n + 1) / 2 * y_ ((n + 1) + i ) (/sqrt 2) -
             agmpi (n + 1) / 2 * y_ ((n + 1) + i + 1) (/sqrt 2)) p).
    induction p as [ | p IH].
      assert (help : forall f, sum_f_R0 f 0 = f 0%nat) by reflexivity.
      rewrite -> !help, plus_0_r.
      replace (n + 1 + 1)%nat with (S (n + 1)) by ring.
      now rewrite <- Rmult_minus_distr_l; destruct (step1 _ n2) as [_ st].
    assert (help : forall m f, sum_f_R0 f (S m) = sum_f_R0 f m + f (S m))
     by reflexivity.
    rewrite -> !help; apply Rplus_le_compat;[apply IH | ].
    replace (n + 1 + S p + 1)%nat with (S (n + 1 + S p)) by ring.
    assert (nsp1 : (1 <= n + 1 + S p)%nat) by lia.
    destruct (step1 _ nsp1) as [_ it]; apply (Rle_trans _ _ _ it).
    rewrite <- Rmult_minus_distr_l.
    apply Rmult_le_compat_r.
      assert (w := ydecr _ nsp1); psatzl R.
    now apply Rmult_le_compat_r;[psatzl R | apply agmpi_decr; lia].
  exact cmp.
assert (step3 : agmpi (n + 1) / 2 * (y_ (n + 1) (/ sqrt 2) - 1) <=
          agmpi (n + 1) * 4 * Rpower 531 (- (2 ^ n))).
  unfold Rdiv; rewrite !(Rmult_assoc (agmpi (n + 1))); apply Rmult_le_compat_l.
    now apply Rlt_le, agm0.
  now assert (t2 := majoration_y_n_vs2 n); psatzl R.
rewrite (Rmult_comm 4).
assert (agmpi (n + 1) - PI <= agmpi 0 * 4 * Rpower 531 (-2 ^ n)).
 apply (Rle_trans _ _ _ step2), (Rle_trans _ _ _ step3).
 apply Rmult_le_compat_r;[apply Rlt_le, exp_pos | ].
 apply Rmult_le_compat_r;[psatzl R | ].
 now apply Rle_trans with (1:= agmpi_decr _ _ n2 (le_n _)), Rlt_le, agmpi_1_0.
split;[ | assumption].
assert (PI <= agmpi (n + 1));[ | psatzl R].
assert (cv_agm' : is_lim_seq (fun n => agmpi (n + 1)) PI).
  now apply is_lim_seq_incr_n, cv_agmpi.
apply (fun h => is_lim_seq_decr_compare _ PI cv_agm' h n).
intros p; destruct (step1 (p + 1)%nat);[lia | ].
replace (S p + 1)%nat with (S (p + 1)) by ring; psatzl R.
Qed.

Lemma iter_million : 0 <= agmpi 20 - PI <= Rpower 10 (-(10 ^ 6 + 10 ^ 4)).
Proof.
assert (big : (1 <= 19)%nat) by lia.
destruct (bound_agmpi _ big) as [p ub]; split;[exact p | ].
apply Rle_trans with (1 := ub).
assert (explb : 25/10 < exp 1) by interval.
assert (lft : 4 * agmpi 0 < exp 3).
  now apply Rlt_trans with (15);[simpl |]; interval.
apply Rle_trans with (exp 3 * Rpower 531 (-2 ^ 19)).
  now apply Rmult_le_compat_r; apply Rlt_le; [apply exp_pos | assumption].
unfold Rpower; rewrite <- exp_plus.
now apply Rlt_le, exp_increasing; interval.
Qed.
