Require Import Psatz Reals Coquelicot.Coquelicot Interval.Interval_tactic
  generalities agmpi.
Coercion INR : nat >-> R.
Open Scope R_scope.

Ltac approx_sqrt :=
 apply Rsqr_incrst_0; rewrite ?Rsqr_sqrt; unfold Rsqr; try apply sqrt_pos;
  psatzl R.

Lemma vs2_bnd : 0 < / sqrt 2 < 1.
Proof. split; interval.  Qed.

Lemma y_s n x (intx : 0 < x < 1) : y_ (S n) x = yfun (y_ n x).
Proof. now replace (S n) with (n + 1)%nat by ring; rewrite y_step. Qed.

Lemma z_s n x (n1 : (1 <= n)%nat) (intx : 0 < x < 1) : z_ (S n) x =
    (1 + z_ n x * y_ n x) / ((1 + z_ n x) * sqrt (y_ n x)).
Proof. now replace (S n) with (n + 1)%nat by ring; rewrite z_step. Qed.

Lemma prod_lb : forall n, (1 <= n)%nat -> 2/3 < agmpi n/(2 + sqrt 2).
Proof.
intros n n1; case (eq_nat_dec n 1) as [nis1 | ngt1];[rewrite nis1; simpl|].
  now rewrite z_1, y_s, y_0; auto using vs2_bnd; unfold yfun; interval.
destruct n as [|k];[lia | replace (S k) with (k + 1)%nat by ring ].
assert (k1 : (1 <= k)%nat) by lia.
assert (t := bound_agmpi _ k1).
apply Rlt_le_trans with (PI / (2 + sqrt 2));[interval | ].
apply Rmult_le_compat_r;[interval | psatzl R].
Qed.

Lemma y_1_ub : y_ 1 (/ sqrt 2) < 1016/1000.
Proof. now rewrite y_s, y_0;[unfold yfun | split]; interval. Qed.


Definition pr p := agmpi p/(2 + sqrt 2).

Lemma pr_step :
  forall p, (1 + y_ (p + 1) (/sqrt 2))/(1 + z_ (p + 1) (/sqrt 2)) * pr p =
     pr (p + 1).
Proof.
intros p; replace (p + 1)%nat with (S p) by ring.
unfold pr; simpl agmpi; unfold Rdiv; ring.
Qed.

Lemma prod_bnd :
  forall n, (1 <= n)%nat -> 2/3 < pr n < 921/1000.
Proof.
intros n p1; unfold pr.
assert (0 < /sqrt 2 < 1) by now split; interval.
assert (n = (pred n + 1)%nat) by now destruct n; lia.
  case (eq_nat_dec n 1).
    intros nis1; rewrite nis1; simpl; rewrite z_1, y_s, y_0; unfold yfun; auto.
    split; interval.
set (k := (n - 1)%nat); assert (nk1 : n = (k + 1)%nat).
  destruct n; simpl; try lia; unfold k.
  now rewrite Nat.add_comm, Nat.sub_succ, Nat.sub_0_r.
intros nn1; assert (k1 : (1 <= k)%nat) by lia.
assert (t := bound_agmpi k k1); rewrite nk1.
split;
  (apply Rmult_lt_reg_r with (2 + sqrt 2);[interval | ];
   unfold Rdiv; rewrite !Rmult_assoc, Rinv_l, Rmult_1_r;[ | interval];
   apply Rplus_lt_reg_r with (-PI)).
  apply Rlt_le_trans with (2 := proj1 t); interval.
apply Rle_lt_trans with (1 := proj2 t).
unfold agmpi, Rpower.
apply Rle_lt_trans with (4 * (2 + sqrt 2) * exp (- 2 ^ 1 * ln 531)).
  apply Rmult_le_compat; [interval | apply Rlt_le, exp_pos| psatzl R |].
  case (eq_nat_dec k 1).
    now intros kis1; rewrite kis1; apply Req_le.
  intros kn1; apply Rlt_le, exp_increasing, Rmult_lt_compat_r;[interval | ].
  now apply Ropp_lt_contravar, Rlt_pow;[psatzl R | lia].
interval.
Qed.

Lemma y_step_decr : forall y, 1 < y -> (1 + y)/(2 * sqrt y) < y.
intros y cy.
assert (1 < sqrt y) by (rewrite <- sqrt_1; apply sqrt_lt_1_alt; psatzl R).
Search _ (Rsqr _ < Rsqr _).
apply Rsqr_incrst_0; try psatzl R.
  rewrite Rsqr_div; try psatzl R.
  rewrite Rsqr_mult, Rsqr_sqrt; try psatzl R.
  apply (Rmult_lt_reg_r (Rsqr 2 * y)); try (unfold Rsqr; psatzl R).
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l; try (unfold Rsqr; psatzl R).
  rewrite Rmult_1_r.
  assert (0 < Rsqr y * (Rsqr 2 * y) - Rsqr (1 + y)); try psatzl R.
  unfold Rsqr; ring_simplify.
  match goal with |- _ < ?a =>
     replace a with ((y - 1) * (4 * y ^ 2 + 3 * y + 1)) by ring end.
  apply Rmult_lt_0_compat;[psatzl R | ].
  repeat apply Rplus_lt_0_compat; try psatzl R.
  apply Rmult_lt_0_compat;[psatzl R | apply pow_lt; psatzl R].
apply Rmult_le_pos;[| apply Rlt_le, Rinv_0_lt_compat]; psatzl R.
Qed.

Lemma y_decr_n :
  forall x p n, 0 < x < 1 -> (1 <= p)%nat ->  (p < n)%nat ->
    y_ n x < y_ p x.
Proof.
intros x p n intx cp.
assert (main : forall k, (1 <= k)%nat -> y_ (S k) x < y_ k x).
  intros k ck; assert (t := y_gt_1 x k intx).
  now rewrite y_s; unfold yfun; auto; apply y_step_decr; auto.
now induction 1;[ | apply Rlt_trans with (2 := IHle)]; apply main; lia.
Qed.

Lemma z_decr_n :
  forall x p n, 0 < x < 1 -> (1 <= p)%nat ->  (p < n)%nat ->
    z_ n x < z_ p x.
Proof.
intros x p n intx cp.
assert (0 < sqrt x) by (apply sqrt_lt_R0; psatzl R).
assert (0 < /sqrt x) by (apply Rinv_0_lt_compat; psatzl R).
assert (yz: forall k, (1 <= k)%nat -> y_ k x <= z_ k x).
 intros k ck; case (eq_nat_dec k 1) as [k1 | kn1].
    rewrite k1; rewrite y_s; auto; unfold yfun.
    unfold y_, u_, v_, z_, u_, v_; simpl.
    assert (dn : Derive (fun x => sqrt (1 * x)) x = / (2 * sqrt x)).
      apply is_derive_unique; auto_derive;[psatzl R | rewrite !Rmult_1_l].
      now field; psatzl R.
    assert (dd : Derive (fun x => (1 + x) / 2) x = / 2).
      now apply is_derive_unique; auto_derive;[auto | field].
    rewrite dn, dd.
    match goal with |- _ <= ?a => replace a with (/sqrt x) end;
      [ | field; apply Rgt_not_eq; auto].
    replace (2 * sqrt (1 / x)) with (2 * /sqrt x)
      by now unfold Rdiv; rewrite Rmult_1_l, inv_sqrt; try tauto.
    unfold Rdiv; rewrite Rinv_mult_distr, Rinv_involutive; try psatzl R.
    apply Rmult_le_reg_r with (/sqrt x);
     [apply Rinv_0_lt_compat, sqrt_lt_R0; psatzl R | ].
    rewrite <- Rinv_mult_distr, sqrt_sqrt; try psatzl R.
    rewrite !Rmult_assoc, Rinv_r, Rmult_1_r; try psatzl R.
    apply Rmult_le_reg_r with 2;[| rewrite !Rmult_assoc, Rinv_l, Rmult_1_r ];
      try psatzl R.
    apply Rmult_le_reg_r with x;[psatzl R | ].
    rewrite Rmult_plus_distr_r, Rmult_assoc, Rinv_l, Rmult_1_r; try psatzl R.
    now rewrite (Rmult_comm (/x)), Rmult_assoc, Rinv_l, Rmult_1_r; psatzl R.
  assert (pk1k : (pred k + 1)%nat = k) by lia.
  assert (pk1 : (1 <= pred k)%nat) by lia.
  destruct (chain_y_z_y x (pred k) intx pk1) as [h1 _].
  now rewrite <- pk1k; assumption.
assert (main : forall k, (1 <= k)%nat -> z_ (S k) x < z_ k x).
  intros k ck; destruct (chain_y_z_y x k intx ck) as [_ h2].
  replace (S k) with (k + 1)%nat by ring; apply Rle_lt_trans with (1 := h2).
  apply Rlt_le_trans with (2 := yz k ck).
  assert (t := y_gt_1 x k intx).
  apply Rsqr_incrst_0.
    rewrite Rsqr_sqrt;[| psatzl R].
    unfold Rsqr; pattern (y_ k x) at 1; rewrite <- Rmult_1_r.
    apply Rmult_lt_compat_l; psatzl R.
    now apply sqrt_pos.
  now psatzl R.
induction 1.
  now apply main; auto.
apply Rlt_trans with (2 := IHle); apply main; lia.
Qed.

Lemma int_z : forall p, (1 <= p)%nat ->
  1 < z_ p (/ sqrt 2) < 6/5.
intros p p1; split; assert (t := vs2_bnd).
  apply Rle_lt_trans with (z_ (p + 1) (/ sqrt 2)).
    now apply Rlt_le, z_gt_1; auto; lia.
  now apply z_decr_n; auto; lia.
assert (z1bnd : z_ 1 (/sqrt 2) < 6/5)
  by now rewrite z_1; auto; interval.
destruct (eq_nat_dec p 1) as [p1' | pn1].
  rewrite p1'; assumption.
apply Rlt_trans with (2 := z1bnd).
apply z_decr_n; auto; lia.
Qed.


Lemma vmapprox: forall x , 0 < x < /2 -> / (1 - x) < 1 + x + 2 * x ^ 2.
Proof.
intros x pe; apply (Rmult_gt_reg_l (1 - x)); try psatzl R.
rewrite Rinv_r; try psatzl R.
replace ((1 - x) * (1 + x + 2 * x ^ 2))
   with (1 + x ^ 2 * ( 1 - 2 * x)) by ring.
pattern 1 at 1; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat;[apply pow_lt | ]; psatzl R.
Qed.

Lemma vpapprox : forall x, 0 < x < /2 -> 1 - x < / (1 + x).
Proof.
intros x ine; apply (Rmult_gt_reg_l (1 + x));[psatzl R | ].
rewrite Rinv_r;[ | psatzl R].
replace ((1 + x) * (1 - x)) with (1 - x^2) by ring.
assert (0 < x ^ 2) by (apply pow_lt; psatzl R); psatzl R.
Qed.

Lemma derive_y_step : forall x, 0 < x ->
  is_derive (fun z => (1 + z) / (2 * sqrt z)) x
    ((x - 1)/(4 * x * sqrt x)).
Proof.
intros x x0; assert (0 < sqrt x) by now apply sqrt_lt_R0.
auto_derive; cycle 1.
  set (u := sqrt x).
  replace x with (sqrt x * sqrt x) by now rewrite sqrt_sqrt; psatzl R.
  now unfold u; clear u; field; apply Rgt_not_eq; auto.
now split;[auto | split;[psatzl R | auto]].
Qed.

Lemma z_step_derive_z  y z : -1 < z -> (0 < y) ->
  is_derive (fun z => (1 + y * z)/((1 + z) * sqrt y)) z
     (sqrt y * (y - 1) / ((1 + z) ^ 2 * y)).
Proof.
intros zm1 y0.
assert (0 < sqrt y) by now apply sqrt_lt_R0.
auto_derive.
  now apply Rgt_not_eq, Rmult_lt_0_compat; psatzl R.
set (u := sqrt y).
replace y with (sqrt y * sqrt y) by now rewrite sqrt_sqrt; psatzl R.
now unfold u; clear u; field; split; apply Rgt_not_eq; psatzl R.
Qed.

(* standard *)
Lemma pow_increasing n x y : (0 < n)%nat -> 0 < x -> x < y -> x ^ n < y ^ n.
Proof.
induction 1 as [ | m mgt0 IH]; [simpl; rewrite !Rmult_1_r; auto | ].
intros x0 xy; simpl; apply Rmult_gt_0_lt_compat.
   apply pow_lt; assumption.
  apply (Rlt_trans _ _ _ x0 xy).
 assumption.
apply IH; assumption.
Qed.


Lemma z_step_derive_y  y z : -1 < z -> (0 < y) ->
  is_derive (fun y => (1 + y * z)/((1 + z) * sqrt y)) y
     ((z * y - 1)/(2 * (1+z) * y * sqrt y)).
Proof.
intros zm1 y0; assert (0 < sqrt y) by now apply sqrt_lt_R0.
auto_derive.
  now split;[| split;[apply Rgt_not_eq, Rmult_lt_0_compat|]]; auto; psatzl R.
set (u := sqrt y).
replace y with (sqrt y * sqrt y) by now rewrite sqrt_sqrt; psatzl R.
now unfold u; field; split; psatzl R.
Qed.

Lemma bound_y_1 : 1 < (1 + sqrt 2)/(2 * sqrt(sqrt 2)) < 51/50.
Proof. split; interval. Qed.

Lemma bound_z_1 : 1 < sqrt(sqrt 2) < 6/5.
Proof. split; interval. Qed.

Lemma MVT_abs : (* standard *)
  forall (f f' : R -> R) (a b : R),
  (forall c : R, Rmin a b <= c <= Rmax a b ->
      derivable_pt_lim f c (f' c)) ->
  exists c : R, Rabs (f b - f a) = Rabs (f' c) * Rabs (b - a) /\
             Rmin a b <= c <= Rmax a b.
Proof.
intros f f' a b.
destruct (Rle_dec a b).
 destruct (Req_dec a b) as [ab | anb].
  unfold Rminus; intros _; exists a; split.
   now rewrite <- ab, !Rplus_opp_r, Rabs_R0, Rmult_0_r.
  split;[apply Rmin_l | apply Rmax_l].
 rewrite Rmax_right, Rmin_left; auto; intros derv.
 destruct (MVT_cor2 f f' a b) as [c [hc intc]];[psatzl R | apply derv | ].
 exists c; rewrite hc, Rabs_mult;split;[reflexivity | psatzl R].
rewrite Rmax_left, Rmin_right; try psatzl R; intros derv.
destruct (MVT_cor2 f f' b a) as [c [hc intc]];[psatzl R | apply derv | ].
exists c; rewrite <- Rabs_Ropp, Ropp_minus_distr, hc, Rabs_mult.
split;[now rewrite <- (Rabs_Ropp (b - a)), Ropp_minus_distr|psatzl R].
Qed.

Lemma qst_derive : forall y z,  -1 < z ->
  is_derive (fun z => (1 + y)/(1 + z)) z (- (1 + y)/(1 + z) ^ 2).
Proof. intros y z z1; auto_derive;[| field]; psatzl R. Qed.

Lemma Rabs_le : forall a b, -b <= a <= b -> Rabs a <= b. (* standard *)
intros a b; unfold Rabs; case Rcase_abs.
 intros _ [it _]; apply Ropp_le_cancel; rewrite Ropp_involutive; exact it.
intros _ [_ it]; exact it.
Qed.

Section rounded_operations.

Variables (e : R) (r_div : R -> R -> R) (r_sqrt : R -> R)
           (r_mult : R -> R -> R).

Hypothesis ce : 0 < e < /1000.

Hypothesis r_mult_spec :
  forall x y, 0 <= x -> 0 <= y -> x * y - e < r_mult x y <= x * y.

Hypothesis r_div_spec :
  forall x y, (0 < y) -> x/y - e < r_div x y <= x/y.

Hypothesis r_sqrt_spec :
  forall x, 0 <= x -> sqrt x - e < r_sqrt x <= sqrt x.


Lemma y_error e' y h :
  (e' < /10) -> (e <= /2 * e') -> 1 < y < 71/50 -> Rabs h < e' ->
  let y1 := (1 + y)/(2 * sqrt y) in
  y1 - e' < r_div (1 + (y + h)) (2 * (r_sqrt (y + h))) < y1 + e'.
Proof.
assert (db1 :
          forall c, 1 <= c < 38/25 -> 0 <= (c - 1) / (4 * c * sqrt c) < 1/8).
 intros c intc.
 assert (1 <= sqrt c).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; psatzl R.
 assert (0 < / (4 * c * sqrt c)).
  now apply Rinv_0_lt_compat, Rmult_lt_0_compat; psatzl R.
 case (Rle_lt_dec c (121/100)); intros b1.
  split.
   now unfold Rdiv; apply Rmult_le_pos; psatzl R.
  apply Rle_lt_trans with (/4 / (4 * 1 * 1)); try psatzl R.
  apply Rmult_le_compat; try psatzl R.
  apply Rle_Rinv; try psatzl R.
   apply Rmult_lt_0_compat; psatzl R.
  apply Rmult_le_compat; psatzl R.
 split.
  now unfold Rdiv; apply Rmult_le_pos; psatzl R.
 apply Rle_lt_trans with (13/25 */ (4 * (121/100) * (11/10))); try psatzl R.
 apply Rmult_le_compat; try psatzl R.
 apply Rle_Rinv; try psatzl R.
  now apply Rmult_lt_0_compat; psatzl R.
 rewrite !Rmult_assoc; repeat apply Rmult_le_compat_l; try psatzl R.
 apply Rmult_le_compat; try psatzl R.
 apply Rsqr_incr_0; try psatzl R.
 rewrite Rsqr_sqrt; unfold Rsqr; psatzl R.
assert (db2 :
        forall c, 9/10 <= c <= 1 -> - /20 < (c - 1) / (4 * c * sqrt c) <= 0).
 intros c intc.
 assert (9/10 < sqrt c).
  apply Rsqr_incrst_0; try psatzl R.
   rewrite Rsqr_sqrt; unfold Rsqr; psatzl R.
  now apply sqrt_pos.
 split.
  apply Ropp_lt_cancel; unfold Rdiv; rewrite Ropp_involutive,
    <- Ropp_mult_distr_l_reverse.
  apply Rle_lt_trans with (/9 * / (4 * (9/10) * (9/10))); try psatzl R.
  apply Rmult_le_compat; try psatzl R.
   now apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; psatzl R.
  apply Rle_Rinv; try psatzl R.
   now apply Rmult_lt_0_compat; psatzl R.
  apply Rmult_le_compat; psatzl R.
 assert (help : forall a, 0 <= -a -> a <= 0) by (intros; psatzl R).
 apply help; clear help; unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse.
 apply Rmult_le_pos;[psatzl R| apply Rlt_le, Rinv_0_lt_compat].
 apply Rmult_lt_0_compat; psatzl R.
intros ce' cc cy ch; lazy zeta.
apply Rabs_def2 in ch.
destruct (r_sqrt_spec (y + h)) as [sc1 sc2]; try psatzl R.
assert (9/10 <= y + h) by psatzl R.
assert (9/10 < sqrt (y + h)).
 apply Rsqr_incrst_0; try psatzl R.
  rewrite Rsqr_sqrt; unfold Rsqr; psatzl R.
 now apply sqrt_pos.
assert (2 * (sqrt (y + h) - e) <= 2 * (r_sqrt (y + h))).
 destruct (r_sqrt_spec (y + h)) as [m1 m2]; psatzl R.
destruct (r_div_spec (1 + (y + h)) (2 * (r_sqrt (y + h))))
  as [dl dh]; try psatzl R.
assert (low : (1 + (y + h)) / (2 * sqrt (y + h)) - e <=
        r_div (1 + (y + h)) (2 * (r_sqrt (y + h)))).
 apply Rle_trans with ((1 + (y + h)) / (2 * (r_sqrt (y + h))) - e).
 apply Rplus_le_compat_r, Rmult_le_compat_l; try psatzl R.
  now apply Rle_Rinv; psatzl R.
 psatzl R.
assert (948/1000 < sqrt (9/10)).
 apply Rsqr_incrst_0; try psatzl R.
  now rewrite Rsqr_sqrt; try psatzl R; unfold Rsqr; psatzl R.
 now apply sqrt_pos.
assert (high1 : r_div (1 + (y + h)) (2 * (r_sqrt (y + h))) <=
               (1 + (y + h)) / (2 * sqrt (y + h) - 2 * e)).
 apply Rle_trans with (1 := dh), Rmult_le_compat_l; try psatzl R.
 now apply Rle_Rinv; psatzl R.
assert (high2 : r_div (1 + (y + h)) (2 * (r_sqrt (y + h))) <=
               (1 + (y + h)) / (2 * sqrt (y + h)) + 3/2 * e).
 apply Rle_trans with (1 := high1).
 (* This is much more than needed, but in case future optimisations need it,
    I prove this stronger result *)
 assert ((1 + (y + h)) / (2 * sqrt (y + h) - 2 * e) <=
         (1 + (y + h)) / (2 * sqrt (y + h)) + 127/100 * e);[|psatzl R].
 unfold Rdiv; replace (/ (2 * sqrt (y + h) - 2 * e)) with
   (/ ((2 * sqrt (y + h))) * / (1 - 2 * e/(2 * sqrt (y + h))))
  by (field; psatzl R).
 rewrite <- Rmult_assoc; set (u := 2 * e/(2 * sqrt (y + h))).
 (* 948/1000 is chose because 948/1000 < sqrt(9/10) *)
 (* 10/9 is chosen because 9/10 <= 1 - e', and 2/(2*(9/10)) = 10/9 *)
 assert (0 < u < 10/9 * e).
  unfold u.
  split.
   now apply Rmult_lt_0_compat; try psatzl R; apply Rinv_0_lt_compat; psatzl R.
  replace (2 * e / (2 * sqrt (y + h))) with (2 / (2 * sqrt (y + h)) * e)
   by (field; psatzl R).
  apply Rmult_lt_compat_r; try psatzl R.
  apply (Rmult_lt_reg_r (2 * sqrt (y + h))); try psatzl R.
  unfold Rdiv at 1; rewrite Rmult_assoc, Rinv_l; try psatzl R.
 assert (0 < u + 2 * u ^ 2).
  apply Rplus_lt_le_0_compat; try psatzl R.
  now apply Rmult_le_pos; try apply pow2_ge_0; psatzl R.
 assert (u + 2 * u ^ 2 <= 124/100 * e).
 (* rounding of (10/9)^2 / 2 * e' *)
  assert (u ^ 2 <= 62/1000 * e).
   apply Rle_trans with ((10/9 * e) ^ 2).
    apply pow_incr; try psatzl R.
   replace ((10 / 9 * e) ^ 2) with ((10/9) ^ 2 * e * e) by ring.
   apply Rmult_le_compat_r; psatzl R.
  psatzl R.
 assert (0 <= (1 + (y + h))/(2 * sqrt (y + h))).
  apply Rmult_le_pos; try psatzl R; apply Rlt_le, Rinv_0_lt_compat; psatzl R.
 apply Rle_trans with ((1 + (y + h))/ (2 * sqrt (y + h)) * (1 + u + 2 *u ^ 2)).
  apply Rmult_le_compat_l;[tauto | ].
  apply Rlt_le, vmapprox; psatzl R.
 rewrite Rplus_assoc, Rmult_plus_distr_l, Rmult_1_r; apply Rplus_le_compat_l.
 assert (big_step : forall y, 9/10 < y < 76/50 -> (1 + y)/(2 * sqrt y) < 1023/1000).
   clear; intros y cy.
   case (Rle_lt_dec y 1).
     intros y1; apply Rlt_trans with ((1 + 9/10) / (2 * sqrt (9/10)));
       [ | interval].
  assert (t : forall c, 9/10 <= c <= y ->
                derivable_pt_lim (fun y => (1 + y)/(2 * sqrt y)) c
                 ((fun x => ((x - 1) / (4 * x * sqrt x))) c)).
    now intros; rewrite <- is_derive_Reals; apply derive_y_step; psatzl R.
  assert (t2 : 9/10 < y) by psatzl R.
  destruct (MVT_cor2 (fun y => (1 + y) / (2 * sqrt y))
                         (fun x => ((x - 1) / (4 * x * sqrt x)))
                 _ _ t2 t) as [c [difeq intc]].
  apply Rminus_lt; rewrite difeq.
  apply Ropp_lt_cancel; rewrite Ropp_0, Ropp_mult_distr_l.
  apply Rmult_lt_0_compat;[ | psatzl R].
  unfold Rdiv; rewrite Ropp_mult_distr_l; apply Rmult_lt_0_compat;[psatzl R |].
  apply Rinv_0_lt_compat, Rmult_lt_0_compat;[| apply sqrt_lt_R0]; psatzl R.
  intro y1; apply Rlt_trans with ((1 + 76/50) / (2 * sqrt (76/50))).
  rewrite Rminus_lt_0.
  assert (t : forall c, y <= c <= 76/50 ->
                derivable_pt_lim (fun y => (1 + y)/(2 * sqrt y)) c
                 ((fun x => ((x - 1) / (4 * x * sqrt x))) c)).
    now intros; rewrite <- is_derive_Reals; apply derive_y_step; psatzl R.
  assert (t2 : y < 76/50) by psatzl R.
  destruct (MVT_cor2 (fun y => (1 + y) / (2 * sqrt y))
                         (fun x => ((x - 1) / (4 * x * sqrt x)))
                 _ _ t2 t) as [c [difeq intc]].
  rewrite difeq.
  apply Rmult_lt_0_compat;[ | psatzl R].
  apply Rmult_lt_0_compat;[psatzl R | ].
  apply Rinv_0_lt_compat, Rmult_lt_0_compat;[psatzl R | ].
  apply sqrt_lt_R0; psatzl R.
  now interval.
 apply Rle_trans with (1023/1000 * (124/100 * e));[ | psatzl R].
 apply Rmult_le_compat; try psatzl R.
  apply Rlt_le, big_step; psatzl R.
split;[apply Rlt_le_trans with (2 := low)
       | apply Rle_lt_trans with (1 := high2)]; clear low high1 high2.
 case (Rle_lt_dec 0 h); intros h0.
  apply Rplus_le_lt_compat; try psatzl R.
  assert (help : forall a b, 0 <= b - a -> a <= b) by (intros; psatzl R).
  apply help; clear help.
  destruct h0 as [hlt0 | h0];[|rewrite <- h0, Rplus_0_r; psatzl R].
  assert (cyh : y < y + h) by psatzl R.
  destruct (MVT_cor2 (fun y => (1 + y)/(2 * sqrt y))
              (fun x => (x - 1) / (4 * x * sqrt x)) y _ cyh) as [c [pc1 pc2]].
   intros; rewrite <- is_derive_Reals; apply derive_y_step; psatzl R.
  rewrite pc1; apply Rmult_le_pos;[apply Rmult_le_pos | ]; try psatzl R.
  apply Rlt_le, Rinv_0_lt_compat; apply Rmult_lt_0_compat; try psatzl R.
  apply sqrt_lt_R0; psatzl R.
 assert (help : forall a b c d, a - c < b - d -> a - b < c - d)
   by (intros; psatzl R); apply help; clear help.
 assert (cyh : y + h < y) by psatzl R.
 destruct (MVT_cor2 (fun y => (1 + y)/(2 * sqrt y))
              (fun x => (x - 1) / (4 * x * sqrt x)) _ _ cyh) as [c [pc1 pc2]].
  intros; rewrite <- is_derive_Reals; apply derive_y_step; psatzl R.
 rewrite pc1.
 case (Rle_lt_dec 1 c); intros c1.
  apply Rle_lt_trans with (/8 * (y - (y + h))); try psatzl R.
  apply Rmult_le_compat_r; try psatzl R.
  destruct (db1 c); psatzl R.
 apply Rle_lt_trans with 0; try psatzl R.
 assert (help : forall a, 0 <= -a -> a <= 0) by (intros; psatzl R).
 apply help; clear help; unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse.
 apply Rmult_le_pos; try psatzl R.
 now destruct (db2 c); psatzl R.
case (Rle_lt_dec 0 h); intros h0.
 destruct h0 as [h0 | h0]; [|rewrite <- h0, Rplus_0_r; psatzl R].
 assert (cyh : y < y + h) by psatzl R.
 destruct (MVT_cor2 (fun y => (1 + y)/(2 * sqrt y))
              (fun x => (x - 1) / (4 * x * sqrt x)) _ _ cyh) as [c [pc1 pc2]].
  intros; rewrite <- is_derive_Reals; apply derive_y_step; psatzl R.
 assert (help : forall a b c d, a - c < d - b -> a + b < c + d)
  by (intros; psatzl R); apply help; clear help; rewrite pc1.
 apply Rle_lt_trans with (/8 * (y + h - y)); try psatzl R.
 apply Rmult_le_compat_r; try psatzl R.
 now destruct (db1 c); psatzl R.
assert (cyh : y + h < y) by psatzl R.
destruct (MVT_cor2 (fun y => (1 + y)/(2 * sqrt y))
             (fun x => (x - 1) / (4 * x * sqrt x)) _ _ cyh) as [c [pc1 pc2]].
  intros; rewrite <- is_derive_Reals; apply derive_y_step; psatzl R.
assert (0 < sqrt c) by (apply sqrt_lt_R0; psatzl R).
assert (0 < 4 * c * sqrt c) by (apply Rmult_lt_0_compat; psatzl R).
assert (help : forall a b c d, b - d < c - a -> a + b < c + d)
  by (intros; psatzl R); apply help; clear help.
rewrite pc1.
case (Rle_lt_dec 1 c); intros c1.
 apply Rlt_le_trans with 0; try psatzl R.
 apply Rmult_le_pos; try psatzl R.
 now destruct (db1 c); psatzl R.
apply Rlt_le_trans with ((-/20) * (y - (y + h))); try psatzl R.
apply Rmult_le_compat_r; try psatzl R.
destruct (db2 c); psatzl R.
Qed.

(* bounds on y and z are chosen to fit the actual values of y_1(1/sqrt 2)
  and z_1(1/sqrt 2). *)
Lemma z_error e' y z h h' :
  (e' < /20) -> (e <= /4 * e') -> 1 < y < 51/50 -> 1 < z < 6/5 ->
  Rabs h < e' -> Rabs h' < e' ->
  let z1 := (1 + y * z)/((1 + z) * sqrt y) in
  z1 - e' < r_div (1 + r_mult (y + h) (z + h'))
                  (r_mult (1 + (z + h')) (r_sqrt (y + h))) < z1 + e'.
Proof.
intros smalle' smalle inty intz he' h'e'; lazy zeta.
apply Rabs_def2 in he'; apply Rabs_def2 in h'e'.
assert (prp : 18/20 < (y + h) * (z + h')).
 apply Rlt_trans with (19/20 * (19/20));[psatzl R | ].
 apply Rmult_le_0_lt_compat; psatzl R.
destruct (r_mult_spec  (y + h) (z + h')) as [nlb nub]; try psatzl R.
destruct (r_sqrt_spec (y + h)) as [slb sub]; try psatzl R.
assert (syhgt99 : 19/20 < sqrt (y + h)) by approx_sqrt.
assert (rslb : 18/20 < r_sqrt (y + h)) by psatzl R.
destruct (r_mult_spec (1 + (z + h')) (r_sqrt (y + h))) as [dlb dub]; try psatzl R.
assert (dlb' : 18/20 < (1 + (z + h')) * (r_sqrt (y + h))).
 rewrite <- (Rmult_1_l (18/20)); apply Rmult_le_0_lt_compat; psatzl R.
destruct (r_div_spec (1 + r_mult (y + h) (z + h'))
            (r_mult (1 + (z + h')) (r_sqrt (y + h)))) as [dvlb dvub]; try psatzl R.
assert (help : forall a b c:R, a - b = c -> a = b + c) by (intros; psatzl R).
assert (help' : forall a b c, a - b = c -> b = a - c) by (intros; psatzl R).
assert (dhp : 0 < (1 + (z + h')) * sqrt (y + h))
   by (apply Rmult_lt_0_compat; psatzl R).
assert (dhpv : 0 < /((1 + (z + h')) * sqrt (y + h)))
 by (apply Rinv_0_lt_compat; assumption).
match goal with |- _ < ?x < _ =>
 assert
 ((1 + (y + h) * (z + h'))/((1 + (z + h')) * sqrt (y + h)) - (31/20) * e < x /\
   x < (1 + (y + h) * (z + h'))/((1 + (z + h')) * sqrt (y + h)) + (35/10) * e)
 as [rndl rndu]
end.
 split.
  apply Rlt_trans with (2 := dvlb).
  assert (rmrn : (1 + (y + h) * (z + h') - e) / r_mult (1 + (z + h')) (r_sqrt (y + h)) <=
   (1 + r_mult (y + h) (z + h')) / r_mult (1 + (z + h')) (r_sqrt (y + h))).
   apply Rmult_le_compat_r;[apply Rlt_le, Rinv_0_lt_compat | ]; psatzl R.
  assert (rmrd : (1 + (y + h) * (z + h') - e) / ((1 + (z + h')) * sqrt (y + h)) <=
        (1 + (y + h) * (z + h') - e) / r_mult (1 + (z + h')) (r_sqrt (y + h))).
   apply Rmult_le_compat_l; try psatzl R.
   apply Rle_Rinv; try psatzl R.
   apply Rle_trans with (1 := dub).
   apply Rmult_le_compat_l; try psatzl R.
  match goal with
   |- ?x - ?y < ?z -?t => assert (x + (t - y) < z);[|psatzl R]
  end.
  apply Rlt_le_trans with (2 := rmrn), Rlt_le_trans with (2 := rmrd).
  clear rmrn rmrd dvub dvlb dlb' dub dlb rslb sub slb nub nlb.
  assert (help'' : forall a b c, (a - b)/c = a/c - b/c)
    by (intros; unfold Rdiv; ring).
  rewrite help''; clear help''.
  assert (e/((1 + (z + h')) * sqrt (y + h)) < e /(39/20 * (19/20))).
   apply Rmult_lt_compat_l; try psatzl R.
   apply Rinv_lt_contravar.
    solve[repeat (apply Rmult_lt_0_compat; try psatzl R)].
   apply Rmult_le_0_lt_compat; psatzl R.
  psatzl R.
 apply Rle_lt_trans with (1 := dvub).
 apply Rle_lt_trans with
   ((1 + (y + h) * (z + h')) / (r_mult (1 + (z + h')) (r_sqrt (y + h)))).
  apply Rmult_le_compat_r;[apply Rlt_le, Rinv_0_lt_compat|]; psatzl R.
 apply Rlt_trans with
  ((1 + (y + h) * (z + h')) / ((1 + (z + h')) * (sqrt (y + h)) - (65/20) * e)).
  apply Rmult_lt_compat_l;[psatzl R | apply Rinv_lt_contravar ].
  assert (39/20 * (19/20) < (1 + (z + h')) * sqrt (y + h)).
   apply Rmult_le_0_lt_compat; psatzl R.
   apply Rmult_lt_0_compat; psatzl R.
  apply Rlt_trans with (2 := dlb).
  apply Rlt_le_trans with ((1 + (z + h')) * (sqrt (y + h) - e) - e).
   rewrite Rmult_minus_distr_l; unfold Rminus; rewrite !Rplus_assoc.
   apply Rplus_lt_compat_l.
   apply Rle_lt_trans with (-((45/20) * e) + -e);[psatzl R | ].
   apply Rplus_lt_compat_r, Ropp_lt_contravar, Rmult_lt_compat_r; psatzl R.
  apply Rplus_le_compat_r, Rmult_le_compat_l; psatzl R.
 replace ((1 + (z + h')) * sqrt (y + h) - 65 / 20 * e) with
   ((1 + (z + h')) * sqrt (y + h) *
      (1 - 65/20 * e /((1 + (z + h')) * sqrt (y + h)))) by (field; psatzl R).
 unfold Rdiv; rewrite Rinv_mult_distr;
  try apply Rgt_not_eq; try apply Rmult_lt_0_compat; try psatzl R.
  rewrite <- Rmult_assoc; match goal with
     |- ?x * /(1 - ?x') < _ => set (u := x); set (v := x')
  end.
  apply Rlt_trans with (u * (1 + v + 2 * v ^ 2)).
   apply Rmult_lt_compat_l;[unfold u; apply Rmult_lt_0_compat; psatzl R | ].
   apply vmapprox; unfold v; split.
    repeat apply Rmult_lt_0_compat; psatzl R.
   apply Rlt_trans with (65 * /20 * e * ( / (39/20 * (19/20))));
    [ | psatzl R].
   apply Rmult_lt_compat_l;[psatzl R | ].
   apply Rinv_1_lt_contravar;[ | apply Rmult_le_0_lt_compat ]; psatzl R.
  rewrite Rplus_assoc, Rmult_plus_distr_l, Rmult_1_r; apply Rplus_lt_compat_l.
  replace (v ^ 2) with
    (65/20 * 65/20 * /((1 + (z + h')) * sqrt (y + h)) ^ 2 * e * e);
  [unfold v|unfold v; field; try psatzl R ].
  rewrite (Rmult_assoc _ e _), (Rmult_comm e), <- !(Rmult_assoc _ _ e).
  rewrite <- Rmult_plus_distr_r, <- (Rmult_assoc _ _ e).
  apply Rmult_lt_compat_r;[psatzl R|].
  apply Rlt_trans with
    (((1 + (51/50 + 2/20) * (25/20))/(39/20 * (19/20))) *
     (65/20 * /(39/20 * (19/20)) +
     (2 * (65/20 * 65/20 * / (39/20 * (19/20)) ^ 2)) * /20));
   [|simpl; psatzl R].
  apply Rmult_le_0_lt_compat; try psatzl R.
     apply Rmult_le_pos; psatzl R.
    apply Rplus_le_le_0_compat; try psatzl R.
    repeat apply Rmult_le_pos; try psatzl R.
    apply Rlt_le, Rinv_0_lt_compat, pow_lt; assumption.
   apply Rmult_le_0_lt_compat; try psatzl R.
    apply Rplus_lt_compat_l, Rmult_le_0_lt_compat; psatzl R.
   apply Rinv_1_lt_contravar; try psatzl R.
   apply Rmult_le_0_lt_compat; psatzl R.
  apply Rplus_lt_compat.
   apply Rmult_lt_compat_l;[| apply Rinv_1_lt_contravar ]; try psatzl R.
   apply Rmult_le_0_lt_compat; psatzl R.
  rewrite !Rmult_assoc; repeat (apply Rmult_lt_compat_l; [psatzl R | ]).
  apply Rmult_le_0_lt_compat; try psatzl R.
   apply Rlt_le, Rinv_0_lt_compat, pow_lt; psatzl R.
  apply Rinv_1_lt_contravar;[simpl; psatzl R | ].
  apply pow_increasing; try lia; try apply Rmult_le_0_lt_compat; psatzl R.
 apply Rlt_trans with (1 - 65/20 * e * / (39/20 * (19/20)));[psatzl R |].
 apply Rplus_lt_compat_l, Ropp_lt_contravar, Rmult_lt_compat_l; try psatzl R.
 apply Rinv_1_lt_contravar;[| apply Rmult_le_0_lt_compat ]; psatzl R.
assert (tmp: forall a b c, a < b -> b < c ->
        forall d e, d < a /\ c < e -> d < b < e) by (intros; psatzl R).
apply tmp with (1:=rndl)(2:=rndu); clear tmp.
assert (ppg : Rabs ((1 + (y + h) * (z + h')) / ((1 + (z + h')) * sqrt (y + h)) -
   (1 + y * z) / ((1 + z) * sqrt y)) <
   (* a bound for the derivative in z.  This is less than 1/40 *)
   26/25 * (7/100) /((38/10) * (19/20)) * e' +
   (* a bound for the derivative in y.  this is less than 1/13 *)
   (120/100 * (107/100) - 1) / (2 * 2 * (19/20) * (19/20)) * e');
  [ | apply Rabs_def2 in ppg; simpl in ppg; psatzl R].
match goal with |- Rabs (?a - ?b) < _ =>
  let v := constr: ((1 + (y + h) * z) / ((1 + z) * sqrt (y + h))) in
  replace (a - b) with (a - v + (v - b)) by ring
end.
assert (sqrt (y + h) < 26/25) by approx_sqrt.
apply Rle_lt_trans with (1 := Rabs_triang _ _); apply Rplus_lt_compat.
 destruct (MVT_abs (fun z => (1 + (y + h) * z)/((1 + z) * sqrt (y + h)))
            (fun z => sqrt (y + h) * ((y + h) - 1) / ((1 + z) ^ 2 * (y + h)))
            z (z + h')) as [c [hc intc]].
  intros c intc; rewrite <- is_derive_Reals.
  apply z_step_derive_z; try psatzl R.
  revert intc; destruct (Rle_dec 0 h');
    [rewrite Rmax_right, Rmin_left | rewrite Rmax_left, Rmin_right];psatzl R.
 assert (19/20 < c).
  revert intc; destruct (Rle_dec 0 h');
    [rewrite Rmin_left | rewrite Rmin_right]; psatzl R.
 assert ( 38/10 < (1 + c) ^ 2).
  apply Rlt_trans with ((39/20) ^ 2);[simpl; psatzl R | ].
  apply pow_increasing; try lia; psatzl R.
 assert (0 < / ((1 + c) ^ 2 * (y + h)) < / ((38/10) * (19/20))).
  split; [apply Rinv_0_lt_compat, Rmult_lt_0_compat; psatzl R | ].
  apply Rinv_1_lt_contravar;[| apply Rmult_le_0_lt_compat]; psatzl R.
 rewrite hc; apply Rmult_le_0_lt_compat; try apply Rabs_pos.
  destruct (Rle_dec 0 (y + h - 1)).
   rewrite Rabs_pos_eq.
    apply Rmult_le_0_lt_compat; repeat apply Rmult_le_pos; try psatzl R.
    apply Rmult_le_0_lt_compat; psatzl R.
   repeat apply Rmult_le_pos; psatzl R.
  unfold Rdiv at 1.
  rewrite <- Rabs_Ropp, Rabs_pos_eq, <- Ropp_mult_distr_l_reverse.
   rewrite <- Ropp_mult_distr_r_reverse.
  apply Rmult_le_0_lt_compat; repeat apply Rmult_le_pos; try psatzl R.
   apply Rmult_le_0_lt_compat; repeat apply Rmult_le_pos; psatzl R.
  rewrite <- Ropp_mult_distr_l_reverse, <- Ropp_mult_distr_r_reverse.
  repeat apply Rmult_le_pos; psatzl R.
 apply Rabs_def1; psatzl R.
destruct (MVT_abs (fun y => (1 + y * z) / ((1 + z) * sqrt y))
                (fun y => ((z * y - 1)/(2 * (1+z) * y * sqrt y)))
                y (y + h)) as [c [hc intc]].
 intros c intc; rewrite <- is_derive_Reals.
 apply z_step_derive_y; try psatzl R.
  revert intc; destruct (Rle_dec 0 h);
  [rewrite Rmin_left, Rmax_right | rewrite Rmin_right, Rmax_left]; psatzl R.
rewrite hc.
apply Rmult_le_0_lt_compat; try apply Rabs_pos;[| apply Rabs_def1; psatzl R].
assert (19/20 < c).
  revert intc; destruct (Rle_dec 0 h);
  [rewrite Rmin_left, Rmax_right | rewrite Rmin_right, Rmax_left]; psatzl R.
assert (19/20 < sqrt c) by approx_sqrt.
assert (0 < / (2 * (1 + z) * c * sqrt c) < /(4 * (19/20) * (19/20))).
 split;[apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat; psatzl R|].
 apply Rinv_1_lt_contravar;[psatzl R | ].
 repeat (apply Rmult_le_0_lt_compat; repeat apply Rmult_le_pos; try psatzl R).
destruct (Rle_dec 0 (z * c - 1)).
 rewrite Rabs_pos_eq;[|repeat apply Rmult_le_pos; psatzl R].
 apply Rmult_le_0_lt_compat; repeat apply Rmult_le_pos; try psatzl R.
 apply Rplus_lt_compat_r.
 apply Rmult_le_0_lt_compat; try psatzl R.
 revert intc; destruct (Rle_dec 0 h);
 [rewrite Rmax_right | rewrite Rmax_left]; psatzl R.
unfold Rdiv at 1; rewrite <- Rabs_Ropp, Rabs_pos_eq.
 rewrite <- Ropp_mult_distr_l_reverse.
 apply Rmult_le_0_lt_compat; repeat apply Rmult_le_pos; try psatzl R.
 apply Rlt_trans with (-(1 * (19/20) - 1));[|psatzl R].
 apply Ropp_lt_contravar, Rplus_lt_compat_r, Rmult_le_0_lt_compat; psatzl R.
rewrite <- Ropp_mult_distr_l_reverse; apply Rmult_le_pos; psatzl R.
Qed.

Lemma qst1 : forall e' y z h h', e' < /40 ->
  Rabs h < /2 * e' -> Rabs h' < e' -> e <= /4 * e' ->
  1 < y < 51/50 -> 1 < z < 6/5 ->
  Rabs (r_div (1 + (y + h)) (1 + (z + h')) - (1 + y)/(1 + z)) <  13/10 * e'.
intros e' y z h h' smalle' smallh smallh' smalle bndy bndz.
apply Rabs_def2 in smallh; apply Rabs_def2 in smallh'.
destruct (r_div_spec (1 + (y + h)) (1 + (z + h'))) as [ld ud]; try psatzl R.
assert (tmp : forall c a b, a - b = a - c + (c - b)) by (intros; ring).
rewrite (tmp ((1 + (y + h))/(1 + (z + h')))).
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (13/10 * e') with (/4 * e' + (21/20 * e')) by field.
apply Rplus_le_lt_compat;[apply Rabs_le; psatzl R | ].
clear ld ud.
rewrite (tmp ((1 + y)/(1 + (z + h')))).
 apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (21/20 * e') with (40/79 * e' + (21/20 - 40/79) * e') by field.
apply Rplus_lt_compat.
 match goal with
   |- Rabs ?x < _ =>
   replace x with (h/(1 + (z + h'))) by (field; psatzl R)
  end.
 unfold Rdiv; rewrite Rabs_mult, Rmult_comm.
 apply Rle_lt_trans with (40/79 * Rabs h).
  apply Rmult_le_compat_r;[apply Rabs_pos | ].
  rewrite Rabs_pos_eq.
   replace (40/79) with (/(79/40)) by field.
   apply Rle_Rinv; psatzl R.
  apply Rlt_le, Rinv_0_lt_compat; psatzl R.
 apply Rmult_lt_compat_l; try apply Rabs_def1; psatzl R.
destruct (MVT_abs (fun z => (1 + y) / (1 + z)) (fun z => -(1 + y)/(1 + z) ^ 2)
                           z (z + h')) as [c [pc intc]].
 intros c intc; rewrite <- is_derive_Reals; apply qst_derive.
 revert intc; destruct (Rle_dec 0 h');[rewrite Rmin_left | rewrite Rmin_right];
 intros; try psatzl R.
rewrite pc; apply Rmult_le_0_lt_compat; try apply Rabs_pos.
unfold Rdiv; rewrite <- Rabs_Ropp, Ropp_mult_distr_l_reverse, Ropp_involutive.
assert (39/40 < c).
 revert intc; destruct (Rle_dec 0 h');[rewrite Rmin_left | rewrite Rmin_right];
 intros; psatzl R.
rewrite Rabs_pos_eq;[ | apply Rmult_le_pos; [psatzl R | ]].
  apply Rlt_le_trans with (101/50 * / (79/40) ^ 2);[ | simpl; psatzl R].
  apply Rmult_le_0_lt_compat; try psatzl R.
   apply Rlt_le, Rinv_0_lt_compat, pow_lt; psatzl R.
  apply Rinv_1_lt_contravar;[simpl; psatzl R | ].
  apply pow_increasing; try lia; psatzl R.
 apply Rlt_le, Rinv_0_lt_compat, pow_lt; psatzl R.
apply Rabs_def1; psatzl R.
Qed.

Lemma product_error_step :
  forall p v e1 e2 h h', 0 <= e1 <= /100 -> 0 <= e2 <= /100 ->
    e < /5 * e2 -> /2 < p < 921/1000 ->
    /2 < v <= 1 -> Rabs h < e1 -> Rabs h' < e2 ->
    Rabs (r_mult (p + h) (v + h') - p * v) < e1 + 23/20 * e2.
Proof.
intros p v e1 e2 h h' smalle1 smalle2 cmpee2 p45 v1 smallh smallh'.
apply Rabs_def2 in smallh; apply Rabs_def2 in smallh'.
replace (r_mult (p + h) (v + h') - p * v) with
   (r_mult (p + h) (v + h') - (p + h) * (v + h') +
    ((p + h) * (v + h') - p * v)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
replace (e1 + 23/20 * e2) with (e + (e1 + 23/20 * e2 - e)) by ring.
apply Rplus_le_lt_compat.
 apply Rabs_le; destruct (r_mult_spec (p + h) (v + h')); psatzl R.
replace ((p + h) * (v + h') - p * v) with ((p + h) * h' + v * h) by ring.
replace (e1 + 23/20 * e2 - e) with (23/20 * e2 - e + (1 * e1)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
 apply Rle_lt_trans with ((921/1000 + /100) * e2);[| psatzl R].
 rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos.
  apply Rabs_le; psatzl R.
 apply Rabs_le; psatzl R.
destruct (Req_dec v 1) as [vq1 | vn1].
 rewrite vq1, Rabs_mult, (Rabs_pos_eq 1), !Rmult_1_l;
 try apply Rabs_def1; psatzl R.
rewrite Rabs_mult; apply Rmult_le_0_lt_compat; try apply Rabs_pos;
 apply Rabs_def1; psatzl R.
Qed.

Fixpoint rpi_rec n y z prod : R :=
  match n with
    0 => r_mult (2 + r_sqrt 2) prod
  | S p =>
    let sy := r_sqrt y in
    let ny := (r_div (1 + y) (2 * (r_sqrt y))) in
    let nz := (r_div (1 + r_mult y z) (r_mult (1 + z) sy)) in
    rpi_rec p  ny nz (r_mult prod (r_div (1 + ny) (1 + nz)))
  end.

Definition ry1 := r_div (1 + r_sqrt 2) (2 * (r_sqrt (r_sqrt 2))).

Definition rz1 := r_sqrt (r_sqrt 2).

Definition rpi1 := r_div (1 + ry1) (1 + rz1).

Definition rpi (n : nat) :=
  match n with
   O => 2 + r_sqrt 2
  | S p => rpi_rec p ry1 rz1 rpi1
  end.

Lemma ry_step : forall p y,
   (1 <= p)%nat ->
   Rabs (y - y_ p (/sqrt 2)) < 2 * e ->
   Rabs (r_div (1 + y) (2 * (r_sqrt y)) - y_ (p + 1) (/sqrt 2)) < 2 * e.
Proof.
intros p y p1 ch.
assert (double_e : 2 * e < / 10) by psatzl R.
set (h := y - y_ p (/sqrt 2)).
assert (double_eK : e <= /2 * (2 * e)) by psatzl R.
set (y' := r_div (1 + y) (2 * (r_sqrt y))).
assert (inty' : 1 < y_ p (/sqrt 2) < 71/50).
 split; [apply y_gt_1, vs2_bnd |  ].
 destruct (eq_nat_dec p 1) as [pq1 | pn1].
  rewrite pq1; apply Rlt_trans with (1 := y_1_ub); psatzl R.
 apply Rlt_trans with (y_ 1 (/sqrt 2));
  [apply y_decr_n; try apply vs2_bnd; try lia; try psatzl R | ].
 apply Rlt_trans with (1 := y_1_ub);psatzl R.
generalize (y_error (2 * e) (y_ p (/sqrt 2)) h double_e double_eK
           inty' ch); lazy zeta.
fold (yfun (y_ p (/sqrt 2))); rewrite <- y_step;[ | exact vs2_bnd].
replace (y_ p (/sqrt 2) + h) with y by (unfold h; ring); fold y'.
intros; apply Rabs_def1; psatzl R.
Qed.

Lemma rz_step :
  forall y z p, (1 <= p)%nat ->
  Rabs (y - y_ p (/sqrt 2)) < 2 * e ->
  Rabs (z - z_ p (/sqrt 2)) < 4 * e ->
  Rabs (r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y)) -
        z_ (p + 1) (/ sqrt 2)) < 4 * e.
intros y z p p1 cy cz.
set (h := y - y_ p (/sqrt 2)).
set (h' := z - z_ p (/sqrt 2)).
assert (cy' : Rabs h < 4 * e) by (unfold h; psatzl R).
assert (vs2 := vs2_bnd).
assert (y1b := y_1_ub).
assert (inty : 1 < y_ p (/sqrt 2) < 51/50).
 split;[apply y_gt_1, vs2_bnd |
  apply Rle_lt_trans with (y_ 1 (/sqrt 2)); try psatzl R].
 destruct (eq_nat_dec p 1) as [pq1 |];
  [rewrite pq1; psatzl R | apply Rlt_le, y_decr_n; auto; lia].
assert (be44 : e <= /4 * (4 * e)) by psatzl R.
assert (four_e : 4 * e < /20) by psatzl R.
generalize (z_error (4 * e) (y_ p (/sqrt 2)) (z_ p (/sqrt 2)) h h'
             four_e be44 inty (int_z p p1) cy' cz).
lazy zeta. rewrite -> (Rmult_comm (y_ p (/sqrt 2)) (z_ p (/sqrt 2))),
   <- z_step; auto.
replace (y_ p (/ sqrt 2) + h) with y by (unfold h; ring).
replace (z_ p (/ sqrt 2) + h') with z by (unfold h'; ring).
intros; apply Rabs_def1; psatzl R.
Qed.

Lemma rprod_step :
  forall p y z prod, (1 <= p)%nat ->
    4 * (3/2) * INR p * e < /100 ->
    Rabs (y - y_ p (/sqrt 2)) < 2 * e ->
    Rabs (z - z_ p (/sqrt 2)) < 4 * e ->
    Rabs (prod - pr p) < 4 * (3/2) * INR p * e ->
   Rabs (r_mult prod (r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
              (1 + r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y))))
          - pr (p + 1)) < 4 * (3/2) * INR (p + 1) * e.
intros p y z prd p1 smallnp cy cz cprd.
assert (four_e : 4 * e < /40) by psatzl R.
assert (vs2 := vs2_bnd).
assert (y1b := y_1_ub).
assert (inty' : 1 < y_ (p + 1) (/sqrt 2) < 51/50).
 split;[apply y_gt_1 | apply Rlt_trans with (y_ 1 (/sqrt 2))]; try psatzl R.
  apply y_decr_n; try psatzl R; try lia.
assert (intz' : 1 < z_ (p + 1) (/ sqrt 2) < 6/5).
 split.
  apply Rle_lt_trans with (z_ ((p + 1) + 1) (/ sqrt 2)).
   apply Rlt_le, z_gt_1; auto; lia.
  apply (z_decr_n (/sqrt 2)); auto; lia.
  apply Rlt_trans with (z_ 1 (/sqrt 2)).
   apply z_decr_n; auto; lia.
  rewrite z_1;[ | split]; interval.
assert (qbnd : Rabs (r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
              (1 + r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y))) -
               ((1 + y_ (p + 1) (/sqrt 2))/(1 + z_ (p + 1) (/sqrt 2))))
           < 13/10 * (4 * e)).
 set (h := r_div (1 + y) (2 * (r_sqrt y)) - y_ (p + 1) (/ sqrt 2)).
 set (h' := r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y)) - z_ (p + 1)
             (/ sqrt 2)).
 assert (cy' : Rabs h < /2 * (4 * e)).
  apply Rlt_le_trans with (1 := ry_step p y p1 cy); psatzl R.
 assert (four_eK : e <= /4 * (4 * e)) by psatzl R.
 generalize (qst1 (4 * e) (y_ (p + 1) (/sqrt 2)) (z_ (p + 1) (/sqrt 2)) h h'
      four_e cy' (rz_step y z p p1 cy cz) four_eK inty' intz').
 replace (y_ (p + 1) (/sqrt 2) + h) with
      (r_div (1 + y) (2 * (r_sqrt y))) by (unfold h; ring).
 replace (z_ (p + 1) (/sqrt 2) + h') with
      (r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y)))
   by (unfold h'; ring).
 solve[auto].
assert (i2 : 0 <= 13/10 * (4 * e) <= /100) by psatzl R.
assert (e5K : e < /5 * (13/10 * (4 * e))) by psatzl R.
set (h := prd - pr p).
set (h' := r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
              (1 + r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y))) -
         (1 + y_ (p + 1) (/ sqrt 2)) / (1 + z_ (p + 1) (/ sqrt 2))).
assert (pb : /2 < pr p < 921/1000) by
  (destruct (prod_bnd _ p1); try psatzl R).
assert (pp1 : (1 <= p + 1)%nat) by lia.
assert (qb : /2 < (1 + y_ (p + 1) (/ sqrt 2))
               / (1 + z_ (p + 1) (/ sqrt 2)) <= 1).
 split.
  apply Rlt_trans with (2/3);[psatzl R | ].
  apply Rmult_le_0_lt_compat; try psatzl R.
  apply Rinv_1_lt_contravar; try psatzl R.
 rewrite <- Rcomplements.Rdiv_le_1;[apply Rplus_le_compat_l | ].
  destruct (chain_y_z_y (/sqrt 2) p vs2 p1); assumption.
 assert (t := z_gt_1 _ _ vs2 pp1); psatzl R.
assert (inte : 0 <= 4 * (3/2) * INR p * e <= /100).
 split;repeat apply Rmult_le_pos; try apply pos_INR; psatzl R.
generalize (product_error_step (pr p) _
              _ (13/10 * (4 * e)) h h' inte i2 e5K pb qb cprd qbnd).
replace (pr p + h) with prd by (unfold h; ring).
replace ((1 + y_ (p + 1) (/sqrt 2)) / (1 + z_ (p + 1) (/ sqrt 2)) + h') with
          (r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
             (1 + r_div (1 + r_mult y z) (r_mult (1 + z) (r_sqrt y))))
   by (unfold h'; ring).
rewrite <- pr_step, <- (Rmult_comm (pr p)).
intros t; apply Rlt_le_trans with (1 := t).
 rewrite plus_INR, (Rmult_plus_distr_l _ (INR p) (INR 1)),
   (Rmult_plus_distr_r _ _ e); simpl (INR 1); psatzl R.
Qed.

Lemma rpi_rec_correct :
  forall p n y z prod,
    (1 <= p)%nat -> 4 * (3/2) * INR (p + n) * e < /100 ->
    Rabs (y - y_ p (/sqrt 2)) < 2 * e -> Rabs (z - z_ p (/sqrt 2)) < 4 * e ->
    Rabs (prod - pr p) < 4 * (3/2) * INR p * e ->
    Rabs (rpi_rec n y z prod - agmpi (p + n)) <
      (2 + sqrt 2) * 4 * (3/2) * INR (p + n) * e + 2 * e.
Proof.
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; approx_sqrt).
assert (1189/1000 < sqrt (sqrt 2)) by approx_sqrt.
intros p n; revert p; induction n.
 intros p y z prd p1; rewrite <- plus_n_O; intros smallp rny rnz rnpr.
 simpl rpi_rec.
 replace (r_mult (2 + r_sqrt 2) prd - agmpi p) with
  ((r_mult (2 + r_sqrt 2) prd - (2 + r_sqrt 2) * prd) +
    ((2 + r_sqrt 2) * prd - (2 + sqrt 2) * prd) +
   ((2 + sqrt 2) * prd - agmpi p)) by ring.
 apply Rle_lt_trans with (1 := Rabs_triang _ _).
 rewrite <- (Rplus_comm (2 * e)).
 apply Rplus_le_lt_compat.
 assert (twop : 0 <= 2) by psatzl R.
 destruct (prod_bnd p p1).
 destruct (r_sqrt_spec 2 twop).
  replace (2 * e) with (e + 1 * e) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_compat.
    apply Rabs_def2 in rnpr.
    destruct (r_mult_spec (2 + r_sqrt 2) prd) as [ml mu]; try psatzl R.
   apply Rabs_le; psatzl R.
  rewrite <- !(Rmult_comm prd), <- Rmult_minus_distr_l, Rabs_mult.
  apply Rmult_le_compat; try apply Rabs_pos.
   replace prd with (prd - pr p + pr p) by ring.
   apply Rle_trans with (1 := Rabs_triang _ _).
   replace 1 with (/20 + 19/20) by field.
   apply Rplus_le_compat.
    apply Rle_trans with (1 := Rlt_le _ _ rnpr); psatzl R.
   destruct (prod_bnd p p1); apply Rabs_le; psatzl R.
  apply Rabs_le; psatzl R.
 replace (agmpi p) with ((2 + sqrt 2) * pr p) by (unfold pr; field; psatzl R).
 rewrite <- Rmult_minus_distr_l, Rabs_mult, Rabs_pos_eq;[|psatzl R].
 repeat rewrite (Rmult_assoc (2 + sqrt 2)); apply Rmult_lt_compat_l; lt0.
intros p y z prd p1 pnsmall cy cz cprd; simpl.
assert (inty : 1 < y_ p (/sqrt 2) < 51/50).
 assert (t := vs2_bnd).
 split;[apply y_gt_1; psatzl R | ].
 apply Rle_lt_trans with (y_ 1 (/sqrt 2)).
  destruct (eq_nat_dec p 1) as [p1' | pn1].
   solve[rewrite p1'; apply Req_le; auto].
  apply Rlt_le, y_decr_n; try psatzl R; try lia.
 rewrite y_s; unfold yfun; auto; rewrite y_0.
 interval.
assert (intz := int_z p).
assert (intz' := int_z (p + 1)).
assert (ce' : 4 * (3/2) * INR p * e < /100).
 apply Rle_lt_trans with (2 := pnsmall).
 apply Rmult_le_compat_r; try psatzl R.
 apply Rmult_le_compat_l; try psatzl R.
 apply le_INR; lia.
assert (cvpn : (p + S n = S p + n)%nat) by ring.
assert (step_y := ry_step p y p1 cy).
assert (step_z := rz_step y z p p1 cy cz).
assert (step_prd := rprod_step p y z prd p1 ce' cy cz cprd).
rewrite cvpn; apply IHn; try (replace (S p) with (p + 1)%nat by ring; assumption).
 lia.
rewrite <- cvpn; assumption.
Qed.

Lemma ry1_correct : Rabs (ry1 - y_ 1 (/sqrt 2)) < 2 * e.
assert (sqrt 2 - e <= r_sqrt 2 <= sqrt 2).
 assert (two_0 : 0 <= 2) by psatzl R.
 destruct (r_sqrt_spec 2 two_0); psatzl R.
assert (double_e_10 : 2 * e < /10) by psatzl R.
assert (double_eK : e <= /2 * (2 * e)) by psatzl R.
assert (ints2 : 1 < sqrt 2 < 71/50) by (split; approx_sqrt).
assert (e0 : Rabs (r_sqrt 2 - sqrt 2) < 2 * e).
 apply Rabs_def1; psatzl R.
generalize (y_error (2 * e) (sqrt 2) (r_sqrt 2 - sqrt 2) double_e_10
          double_eK ints2 e0); lazy zeta.
replace (sqrt 2 + (r_sqrt 2 - sqrt 2)) with (r_sqrt 2) by ring.
fold ry1.
rewrite y_s, y_0; unfold yfun.
 intros; apply Rabs_def1; psatzl R.
split; [apply Rinv_0_lt_compat; psatzl R | ].
pattern 1 at 3; rewrite <- Rinv_1; apply Rinv_1_lt_contravar; psatzl R.
Qed.

Lemma rz1_correct : Rabs (rz1 - z_ 1 (/sqrt 2)) < 4 * e.
Proof.
unfold rz1; rewrite z_1;[|split;interval].
assert (two_0 : 0 <= 2) by psatzl R.
destruct (r_sqrt_spec _ two_0).
assert (141/100 < sqrt 2 < 142/100) by (split; interval).
assert (1 < r_sqrt 2 < 142/100) by psatzl R.
assert (rs2_0 : 0 <= r_sqrt 2) by psatzl R.
destruct (r_sqrt_spec _ rs2_0).
rewrite inv_sqrt, Rinv_involutive;[ | interval | interval].
replace (r_sqrt (r_sqrt 2) - sqrt (sqrt 2)) with
 (r_sqrt (r_sqrt 2) - sqrt(r_sqrt 2) +
  (sqrt (r_sqrt 2) - sqrt (sqrt 2))) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (4 * e) with (e + 3 * e) by ring.
apply Rplus_lt_compat.
 apply Rabs_def1; psatzl R.
destruct (MVT_abs sqrt (fun z => /(2 * sqrt z))
                           (sqrt 2) (r_sqrt 2)) as [c [pc intc]].
 rewrite Rmin_right, Rmax_left; try psatzl R.
 intros c intc; apply derivable_pt_lim_sqrt; psatzl R.
revert intc; rewrite Rmin_right, Rmax_left; try psatzl R; intros intc.
rewrite pc, Rabs_pos_eq, <- Rabs_Ropp, Ropp_minus_distr, Rabs_pos_eq;
 try psatzl R.
 apply Rle_lt_trans with (/ (2 * 1) * (sqrt 2 - r_sqrt 2)); try psatzl R.
 apply Rmult_le_compat_r;[ | apply Rle_Rinv]; try psatzl R.
  apply Rmult_lt_0_compat; try apply sqrt_lt_R0; try psatzl R.
 apply Rmult_le_compat_l; try psatzl R.
 rewrite <- sqrt_1; apply sqrt_le_1_alt; psatzl R.
apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; try psatzl R.
apply sqrt_lt_R0; psatzl R.
Qed.

Lemma ry1_bnd : 1007/1000 < ry1 < 52/50.
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; approx_sqrt).
assert (1410/1000 < r_sqrt 2 < 1415/1000).
 destruct (r_sqrt_spec 2); psatzl R.
assert (1187/1000 < sqrt (r_sqrt 2) < 11896/10000)
   by (split; approx_sqrt).
assert (1183/1000 < r_sqrt (r_sqrt 2) < 119/100).
 destruct (r_sqrt_spec (r_sqrt 2)); psatzl R.
split.
 apply Rlt_trans with ((1 + 141/100)/(2 * (119/100)) - e);[psatzl R | ].
 unfold ry1.
 assert (0 < 2 * (r_sqrt (r_sqrt 2))) by psatzl R.
 destruct (r_div_spec (1 + r_sqrt 2) (2 * (r_sqrt (r_sqrt 2))))
   as [ld ud]; try psatzl R.
 apply Rlt_trans with (2 := ld), Rplus_lt_compat_r.
 apply Rmult_le_0_lt_compat; try psatzl R.
 apply Rinv_1_lt_contravar; psatzl R.
unfold ry1.
destruct (r_div_spec (1 + r_sqrt 2) (2 * (r_sqrt (r_sqrt 2))));
 try psatzl R.
apply Rlt_trans with ((1 + 1415/1000) / (1999/1000 * (1183/1000)));[|psatzl R].
apply Rle_lt_trans with ((1 + r_sqrt 2) / (2 * (r_sqrt (r_sqrt 2))));
 [assumption | ].
apply Rmult_le_0_lt_compat; try psatzl R.
 apply Rlt_le, Rinv_0_lt_compat; psatzl R.
apply Rinv_1_lt_contravar; psatzl R.
Qed.

Lemma rz1_bnd : 1183/1000 < rz1 < 119/100.
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; approx_sqrt).
assert (141/100 < r_sqrt 2 < 1415/1000).
 destruct (r_sqrt_spec 2); psatzl R.
unfold rz1.
assert (1187/1000 < sqrt (r_sqrt 2) < 119/100)
 by (split; approx_sqrt).
 destruct (r_sqrt_spec (r_sqrt 2)); psatzl R.
Qed.

Lemma q1_bnd : 90/100 < r_div (1 + ry1) (1 + rz1) < 94/100.
assert (ty := ry1_bnd).
assert (tz := rz1_bnd).
destruct (r_div_spec (1 + ry1) (1 + rz1)) as [ld ud]; try psatzl R.
split.
 apply Rlt_trans with ((1999/1000)/(1 + 119/100));[psatzl R | ].
 replace ((1999/1000)/(1+119/100)) with
  ((1 + 1007/1000) /(1 + 119/100) - 8/1000 /(1+119/100))
    by field.
 apply Rlt_trans with (2 := ld), Rplus_lt_compat; try psatzl R.
 apply Rmult_le_0_lt_compat; try psatzl R.
 apply Rinv_1_lt_contravar; psatzl R.
apply Rle_lt_trans with (1 := ud).
apply Rlt_trans with ((1 + 52/50)/(1+1183/1000));[|psatzl R].
apply Rmult_le_0_lt_compat; try psatzl R.
 apply Rlt_le, Rinv_0_lt_compat; psatzl R.
apply Rinv_1_lt_contravar; psatzl R.
Qed.

Lemma rpi1_correct : Rabs (rpi1 - pr 1) < 4 * (3/2) * e.
assert (141/100 < sqrt 2 < 142/100) by (split; approx_sqrt).
assert (bnd_z1 : 1 < z_ 1 (/ sqrt 2) < 6/5).
  now rewrite z_1;[split | split]; interval.
replace (pr 1) with ((1 + y_ 1 (/sqrt 2)) / (1 + z_ 1 (/sqrt 2)))
 by (unfold pr; simpl; field; psatzl R).
assert (ty := ry1_correct).
assert (tz := rz1_correct).
set (h := ry1 - y_ 1 (/sqrt 2)).
set (h' := rz1 - z_ 1 (/sqrt 2)).
assert (ty' : Rabs h < /2 * (4 * e))
  by (apply Rlt_le_trans with (1 := ty); psatzl R).
assert (four_e : 4 * e < /40) by psatzl R.
assert (four_eK : e <= /4 * (4 * e)) by psatzl R.
assert (bnd_y1 : 1 < y_ 1 (/sqrt 2) < 51/50).
  now rewrite y_s, y_0; unfold yfun; split; interval.
generalize (qst1 (4 * e) (y_ 1 (/sqrt 2)) (z_ 1 (/sqrt 2)) h h' four_e
         ty' tz four_eK bnd_y1 bnd_z1).
replace (1 + (y_ 1 (/ sqrt 2) + h)) with (1 + ry1) by (unfold h; ring).
replace (1 + (z_ 1 (/ sqrt 2) + h')) with (1 + rz1) by (unfold h'; ring).
intros; unfold rpi1; psatzl R.
Qed.

Lemma rpi_correct : forall n, (1 <= n)%nat -> 6 * n * e < /100 ->
  Rabs (rpi n - agmpi n) < (21 * n + 2) * e.
Proof.
pattern 6 at 1; replace 6 with (4 * (3 / 2)) by field.
intros [|p] p1 cpe; [lia | ]; unfold rpi.
rewrite (Rmult_plus_distr_r _ _ e).
assert (rpi1_correct' : Rabs (rpi1 - pr 1) < 4 * (3 / 2) * INR 1 * e).
 simpl INR; rewrite Rmult_1_r; exact rpi1_correct.
generalize (rpi_rec_correct 1 p ry1 rz1 rpi1 (le_n _) cpe
           ry1_correct rz1_correct rpi1_correct').
intros t; apply Rlt_trans with (1 := t), Rplus_lt_compat_r.
repeat apply Rmult_lt_compat_r; try psatzl R.
 apply (lt_INR 0); lia.
assert (sqrt 2 < 1415/1000) by approx_sqrt; psatzl R.
Qed.

Lemma atan_lt_x : forall x, 0 < x -> atan x < x.
intros x x0.
destruct (MVT_cor2 atan (fun x => /(1 + x ^ 2)) 0 x) as [c [p1 p2]]; auto.
 solve[intros; apply derivable_pt_lim_atan].
replace (atan x) with (atan x - atan 0) by (rewrite atan_0;ring).
 rewrite p1, Rminus_0_r.
pattern x at 2; replace x with (1 * x) by ring.
apply Rmult_lt_compat_r;[assumption | ].
pattern 1 at 2; rewrite <- Rinv_1.
pattern 1 at 2; rewrite <- (Rplus_0_r 1).
apply Rinv_lt_contravar;[apply Rmult_lt_0_compat | ].
  lt0.
 lt0.
apply Rplus_lt_compat_l; lt0.
Qed.

Lemma PI_lt_10_3 : PI < 10/3.
replace PI with (4 * (PI/4)) by field; rewrite Machin_2_3.
replace (10/3) with ((4 * /2) + (4 * /3)) by field.
assert (t1 : 0 < /2) by psatzl R.
assert (t2 : 0 < /3) by psatzl R.
apply atan_lt_x in t1; apply atan_lt_x in t2.
psatzl R.
Qed.

Lemma precision_correct :
  forall n, (2 <= n)%nat -> (6 * n * e < / 100) ->
  Rabs (rpi n - PI) < agmpi n - PI + (21 * n + 2) * e.
Proof.
intros n n1 small_error.
assert (small_error' : 6 * n * e < /100).
 apply Rle_lt_trans with (2 := small_error).
 assert (0 <= INR (n + 1)) by apply pos_INR.
 repeat (apply Rmult_le_compat_r;[psatzl R | ]); psatzl R.
replace (rpi n - PI) with ((agmpi n - PI) + (rpi n - agmpi n)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_le_lt_compat.
 rewrite Rabs_pos_eq;[apply Req_le; reflexivity | ].
 destruct n as [ | n].
  simpl.
  assert (t := PI_lt_10_3).
  assert (7/5 < sqrt 2) by approx_sqrt.
  psatzl R.
  assert (n1' : (1 <= n)%nat) by lia.
  destruct (bound_agmpi n n1'); replace (S n) with (n + 1)%nat by ring.
  assumption.
apply rpi_correct;[lia | assumption].
Qed.

Lemma million_correct :
  e = Rpower 10 (-(10 ^ 6 + 4)) ->
  Rabs (rpi 20 - PI) < /10 * Rpower 10 (-(10 ^ 6)).
intros em.
assert (e < /100000).
 rewrite em, Rpower_Ropp, Rpower_plus, Rinv_mult_distr.
   replace (/100000) with (/Rpower 10 1 */Rpower 10 4).
    apply Rmult_lt_compat_r.
     solve[apply Rinv_0_lt_compat, exp_pos].
    rewrite <- !Rpower_Ropp; apply exp_increasing.
    rewrite !Ropp_mult_distr_l_reverse.
    apply Ropp_lt_contravar, Rmult_lt_compat_r.
     rewrite <- ln_1; apply ln_increasing; psatzl R.
    pattern 1 at 1; rewrite <- (pow_O 10); apply Rlt_pow;[psatzl R | lia].
    pattern 4 at 3; replace 4 with (INR 4) by (simpl; ring).
   rewrite Rpower_pow, Rpower_1; simpl; psatzl R.
  apply Rgt_not_eq, exp_pos.
 apply Rgt_not_eq, exp_pos.
assert (toe : (21 * 20 + 3) * e < /10 * Rpower 10 (- 10 ^ 6)).
 rewrite em, Ropp_plus_distr, Rpower_plus, (Rmult_comm (Rpower _ _)).
 rewrite <- Rmult_assoc; apply Rmult_lt_compat_r.
  solve[unfold Rpower; apply exp_pos].
 replace (-4) with (-INR 4) by (simpl; ring).
 rewrite Rpower_Ropp, Rpower_pow; simpl; psatzl R.
apply Rlt_trans with (2 := toe).
assert (twenty_1 : (1 <= 20)%nat) by lia.
assert (c20e : 6 * INR 20 * e < /100) by (simpl INR; psatzl R).
replace ((21 * 20 + 3) * e) with ((21 * INR 20 + 2) * e + e)
   by (simpl; psatzl R).
assert (help : forall a b c, b - c = b - a + (a - c)) by (intros; ring).
rewrite (help (agmpi 20)).
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_lt_compat.
 exact (rpi_correct 20 twenty_1 c20e).
destruct iter_million as [lb ub] .
rewrite Rabs_pos_eq, em; assumption.
Qed.

End rounded_operations.

Require Import ZArith.

Section high_precision.

Variable precision : Z.
Close Scope R_scope.
Open Scope Z_scope.

Hypothesis big_precision : 1000 < precision.
Hypothesis pos_precision : 0 < precision.

Definition hmult x y := x * y / precision.
Definition hsqrt x := Z.sqrt(precision * x).
Definition hdiv x y := (x * precision)/y.
Definition h1 := precision.
Definition h2 := 2 * h1.

(* These few lines to make the code robust to a bug present in
 coq-8.4pl2, but not in later versions of Coq. *)
Definition floor : R -> Z := Rcomplements.floor.

Lemma floorP (x : R) :  (IZR (floor x) <= x < IZR (floor x) + 1)%R.
Proof.
unfold floor, Rcomplements.floor.
destruct floor_ex as [v vp]; simpl; psatzl R.
Qed.

Definition hR (v : Z) : R := (IZR v /IZR precision)%R.

Definition RbZ (v : R) : Z := floor v.

Definition Rh (v : R) : Z := RbZ( v * IZR precision).


Fixpoint hpi_rec (n : nat) (y z prod : Z) : Z :=
  match n with
    0%nat => hmult (h2 + hsqrt h2) prod
  | S p =>
    let sy := hsqrt y in let ny := hdiv (h1 + y) (2 * sy) in
    let nz := hdiv (h1 + hmult y z) (hmult (h1 + z) sy) in
    hpi_rec p ny nz (hmult prod (hdiv (h1 + ny) (h1 + nz)))
  end.

Definition r_div (x y : R) := hR (Rh (x / y)).

Definition r_mult (x y : R) : R := hR (Rh (x * y)).

Definition r_sqrt (x : R) : R := hR (Rh (sqrt x)).

Lemma hdiv_spec :
  forall x y : Z, 0 < y -> hR (hdiv x y) = r_div (hR x) (hR y).
intros x y y0; unfold hdiv, r_div, hR.
replace (IZR x/ IZR precision / (IZR y / IZR precision))%R with
 (IZR x / IZR y)%R by
   (field; split; apply Rgt_not_eq, (IZR_lt 0); assumption).
apply f_equal with (f := fun x => (IZR x / IZR precision)%R).
unfold Rh, RbZ.
replace (IZR x/IZR y * IZR precision)%R with
  (IZR x * IZR precision/IZR y)%R
 by (field; apply Rgt_not_eq, (IZR_lt 0); assumption).
rewrite <- mult_IZR.
assert (t := Z.div_unique_pos).
set (v := (IZR (x * precision) / IZR y)%R).
destruct (floorP v) as [qle qcl].
simpl; symmetry; apply Z.div_unique_pos with
  (x * precision - floor v * y)%Z; try ring.
assert (floor v * y <= x * precision)%Z.
 apply le_IZR; rewrite mult_IZR; apply Rmult_le_reg_r with (/IZR y)%R.
  apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
 rewrite Rmult_assoc, Rinv_r, Rmult_1_r;[exact qle | ].
 apply Rgt_not_eq, (IZR_lt 0); assumption.
split;[lia | ].
assert (x * precision < floor v * y + y)%Z;[ | lia].
apply lt_IZR; rewrite plus_IZR; apply Rmult_lt_reg_r with (/IZR y)%R.
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
rewrite Rmult_plus_distr_r, (mult_IZR (floor v)).
rewrite Rmult_assoc, Rinv_r, Rmult_1_r.
 assumption.
apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma hmult_spec :
  forall x y : Z, (0 <= x -> 0 <= y ->
   hR (hmult x y) = r_mult (hR x) (hR y))%Z.
intros x y x0 y0; unfold hmult, r_mult, hR.
replace (IZR x / IZR precision * (IZR y /IZR precision))%R
 with (IZR x * IZR y /(IZR precision*IZR precision))%R;
[|field;apply Rgt_not_eq, (IZR_lt 0); assumption].
apply f_equal with (f := (fun x => IZR x /IZR precision)%R).
unfold Rh, RbZ.
match goal with |- context[floor ?a] => set (v := a) end.
destruct (floorP v) as [qle qcl].
symmetry.
apply Z.div_unique_pos with (x * y - floor v * precision); try lia.
assert (floor v * precision <= x * y).
 apply le_IZR; rewrite !mult_IZR.
 apply Rmult_le_reg_r with (/IZR precision)%R;
  [apply Rinv_0_lt_compat, (IZR_lt 0); assumption | ].
 rewrite Rmult_assoc, Rinv_r, Rmult_1_r;
  [|apply Rgt_not_eq, (IZR_lt 0); assumption].
apply Rle_trans with (1 := qle); apply Req_le; unfold v; field;
 apply Rgt_not_eq, (IZR_lt 0); assumption.
assert (x * y < floor v * precision + precision);[|lia].
 replace (floor v * precision + precision) with
  ((floor v + 1) * precision) by ring.
apply lt_IZR; rewrite !mult_IZR, plus_IZR.
simpl (IZR 1).
apply Rmult_lt_reg_r with (/IZR precision)%R;
  [apply Rinv_0_lt_compat, (IZR_lt 0); assumption | ].
rewrite (Rmult_assoc (_ + _)), Rinv_r, Rmult_1_r;
 [|apply Rgt_not_eq, (IZR_lt 0); assumption].
apply Rle_lt_trans with (2 := qcl), Req_le; unfold v; field;
apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma hsqrt_spec :
  forall x : Z, (0<= x -> hR (hsqrt x) = r_sqrt (hR x))%Z.
intros x x0; unfold hsqrt, r_sqrt, hR.
assert (0 < IZR precision)%R by (apply (IZR_lt 0); assumption).
(* TODO : understand why f_equal does not work here *)
replace (Z.sqrt (precision * x)) with
  (Rh (sqrt (IZR x / IZR precision)));[reflexivity | ].
unfold Rh, RbZ;
match goal with |- context[floor ?a] => set (v := a) end.
destruct (floorP v) as [vle vcl].
symmetry; apply Z.sqrt_unique; split.
 apply le_IZR; rewrite mult_IZR.
 apply sqrt_le_0;[apply Rle_0_sqr | | ].
  rewrite mult_IZR; apply Rmult_le_pos.
   apply Rlt_le; assumption.
  apply (IZR_le 0); assumption.
 rewrite sqrt_square.
  apply Rle_trans with (1 := vle), Req_le.
  unfold v; rewrite sqrt_div_alt;[ | assumption].
 unfold Rdiv; rewrite Rmult_assoc.
  pattern (IZR precision) at 2;
  replace (IZR precision) with (sqrt(IZR precision) * sqrt(IZR precision))%R.
   rewrite  <- (Rmult_assoc (/ _)), Rinv_l, Rmult_1_l.
    rewrite <- sqrt_mult, <- mult_IZR, Zmult_comm.
      reflexivity.
     apply (IZR_le 0); assumption.
    apply Rlt_le; assumption.
   apply Rgt_not_eq, sqrt_lt_R0; assumption.
  apply sqrt_sqrt, Rlt_le; assumption.
 apply (IZR_le 0); assert (0 < floor v + 1)%Z;[ | lia].
 apply (lt_IZR 0); rewrite plus_IZR; simpl (IZR 0).
 apply Rle_lt_trans with (2 := vcl).
 apply Rmult_le_pos;[apply sqrt_pos |apply Rlt_le; assumption].
apply lt_IZR; rewrite (mult_IZR (Z.succ _)), succ_IZR.
revert vcl; unfold v; rewrite sqrt_div_alt;[|assumption].
unfold Rdiv; pattern (IZR precision) at 2;
replace (IZR precision) with (sqrt(IZR precision) * sqrt(IZR precision))%R.
 rewrite Rmult_assoc, <- (Rmult_assoc (/sqrt(IZR precision))),
 Rinv_l, Rmult_1_l.
  intros vcl; apply sqrt_lt_0_alt; rewrite sqrt_square.
   rewrite mult_IZR, sqrt_mult, Rmult_comm.
     exact vcl.
    apply Rlt_le; assumption.
   apply (IZR_le 0); assumption.
  apply Rlt_le, Rle_lt_trans with (2 := vcl).
  solve[apply Rmult_le_pos; apply sqrt_pos].
 apply Rgt_not_eq, sqrt_lt_R0; assumption.
rewrite sqrt_sqrt;[reflexivity | apply Rlt_le; assumption].
Qed.

Lemma hdiv_pos :
  forall x y, (0 <= x -> 0 < y -> 0 <= hdiv x y).
Proof.
intros x y x0 y0; unfold hdiv.
apply Z.div_pos.
 apply Z.mul_nonneg_nonneg.
  assumption.
 apply Z.lt_le_incl; assumption.
assumption.
Qed.

Lemma hmult_pos :
  forall x y, 0 <= x -> 0 <= y -> 0 <= hmult x y.
Proof.
intros x y x0 y0; unfold hmult.
apply Z.div_pos.
 apply Z.mul_nonneg_nonneg; assumption.
assumption.
Qed.

Lemma hsqrt_pos :
  forall x, 0 <= hsqrt x.
Proof.
intros x; unfold hsqrt; apply Z.sqrt_nonneg.
Qed.

Lemma hR_half_non_zero : forall x, (/2 < hR x)%R -> 0 < x.
intros x cx; apply lt_IZR.
simpl (IZR 0).
unfold hR in cx; apply Rmult_lt_reg_r with (/IZR precision)%R.
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
apply Rlt_trans with (2 := cx); rewrite Rmult_0_l; psatzl R.
Qed.

Lemma hplus_spec : forall x y, (hR (x + y) = hR x + hR y)%R.
Proof.
intros; unfold hR, Rdiv.
rewrite plus_IZR, Rmult_plus_distr_r; reflexivity.
Qed.

Lemma hscal2_spec : forall x, (hR (2 * x) = 2 * hR x)%R.
Proof.
intros; unfold hR, Rdiv.
rewrite mult_IZR, Rmult_assoc; reflexivity.
Qed.

Lemma h1_spec : hR h1 = 1%R.
Proof.
unfold hR, Rdiv; apply Rinv_r; apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma h2_spec : hR h2 = 2%R.
Proof.
unfold hR, Rdiv, h2, h1; rewrite mult_IZR; simpl (IZR 2).
field; apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma hR_gt_0 : forall x, (0 < hR x)%R -> 0 < x.
intros x x0; apply (lt_IZR 0); simpl (IZR 0).
apply (Rmult_lt_reg_r (/IZR precision)).
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
rewrite Rmult_0_l; exact x0.
Qed.

Lemma floor_IZR (v : Z) : floor (IZR v) = v.
Proof.
clear.
destruct (floorP (IZR v)) as [xle xcl].
apply le_IZR in xle.
revert xcl; replace 1%R with (IZR 1) by reflexivity; rewrite <- plus_IZR.
intros xcl; apply lt_IZR in xcl; lia.
Qed.

Lemma Rh_hR (v : Z) : Rh (hR v) = v.
Proof.
unfold Rh, RbZ, hR.
replace (IZR v / IZR precision * IZR precision)%R with (IZR v)%R.
 rewrite floor_IZR; reflexivity.
field; apply Rgt_not_eq, (IZR_lt 0); exact pos_precision.
Qed.

Lemma hR_pos : forall x, (0 <= hR x)%R -> 0 <= x.
intros x x0; apply (le_IZR 0); simpl (IZR 0).
apply (Rmult_le_reg_r (/IZR precision)).
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
rewrite Rmult_0_l; exact x0.
Qed.

Lemma h2_pos : 0 < h2.
unfold h2; apply Z.mul_pos_pos.
 reflexivity.
assumption.
Qed.

Lemma h1_pos : 0 < h1.
assumption.
Qed.

Open Scope R_scope.

Lemma pos_precisionR : 0 < IZR precision.
apply (IZR_lt 0); exact pos_precision.
Qed.

Lemma hR_Rh (v : R) : v - /IZR precision < hR (Rh v) <= v.
Proof.
unfold hR, Rh, RbZ.
destruct (floorP (v * IZR precision)) as [xle xcl].
assert (0 < IZR precision).
 apply (IZR_lt 0); exact pos_precision.
split.
 replace (v - / IZR precision) with
   ((v * IZR precision - 1)/IZR precision) by (field; psatzl R).
 apply Rmult_lt_compat_r;[apply Rinv_0_lt_compat | ]; try psatzl R.
apply Rmult_le_reg_r with (IZR precision);[assumption | ].
unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
Qed.

Lemma r_div_spec : forall x y, 0 < y ->
   x / y - /IZR precision < r_div x y <= x / y.
intros x y y0; unfold r_div; apply hR_Rh.
Qed.

Lemma r_mult_spec : forall x y, 0 <= x -> 0 <= y ->
   x * y - /IZR precision < r_mult x y <= x * y.
intros x y x0 y0; unfold r_mult; apply hR_Rh.
Qed.

Lemma r_sqrt_spec : forall x, 0 <= x ->
    sqrt x - /IZR precision < r_sqrt x <= sqrt x.
intros; apply hR_Rh.
Qed.

Lemma dummy : 0 < /IZR precision < /1000.
Proof.
split;[apply Rinv_0_lt_compat, (IZR_lt 0); assumption|].
apply Rinv_1_lt_contravar;[psatzl R | ].
replace 1%R with (IZR 1) by reflexivity;
repeat (rewrite <- plus_IZR || rewrite <- mult_IZR); simpl Zmult.
apply IZR_lt; assumption.
Qed.

Lemma hpi_rpi_rec :
  forall n p y z prod,
    (1 <= p)%nat ->
    4 * (3/2) * INR (p + n) * /IZR precision < /100 ->
    Rabs (hR y - y_ p (/sqrt 2)) < 2 * /IZR precision ->
    Rabs (hR z - z_ p (/sqrt 2)) < 4 * /IZR precision ->
    Rabs (hR prod - pr p) < 4 * (3/2) * INR p * /IZR precision ->
    hR (hpi_rec n y z prod) =
    rpi_rec r_div r_sqrt r_mult n (hR y) (hR z) (hR prod).
assert (/IZR precision < /100).
 apply Rinv_1_lt_contravar;[psatzl R |].
 replace 100 with (IZR 100) by (simpl; psatzl R).
 apply IZR_lt; apply Zlt_trans with 1000%Z;[reflexivity |assumption].
assert (1 < sqrt 2) by approx_sqrt.
assert (0 <= h2)%Z by (apply Z.lt_le_incl, h2_pos).
destruct (r_sqrt_spec 2); try psatzl R.
induction n as [|n IHn]; intros p y z prd p1 smallnp cy cz cprd;
generalize (prod_bnd _ p1); intros.
 simpl.
 rewrite hmult_spec, hplus_spec, hsqrt_spec, h2_spec.
    reflexivity.
   apply Z.lt_le_incl, h2_pos.
  apply Z.add_nonneg_nonneg; auto.
  apply hR_pos;rewrite hsqrt_spec, h2_spec.
   psatzl R.
  apply Z.lt_le_incl, h2_pos.
 apply hR_pos; rewrite <- plus_n_O in smallnp.
(* TODO : remove condition on an arbitrary error in prod_lb and prod_bnd *)
 apply Rabs_def2 in cprd; psatzl R.
assert (0 <= h2)%Z by (apply Z.lt_le_incl, h2_pos).
assert (/4 < hR y).
 apply Rabs_def2 in cy; assert (t:= y_gt_1 (/sqrt 2) p vs2_bnd); psatzl R.
assert (/2 < sqrt (hR y)) by approx_sqrt.
destruct (r_sqrt_spec (hR y)); try psatzl R.
assert (0 <= y)%Z by (apply hR_pos; psatzl R).
assert (0 < hsqrt y)%Z.
 apply hR_gt_0; rewrite hsqrt_spec; try psatzl R; assumption.
assert (0 < 2 * hsqrt y)%Z.
 apply Z.mul_pos_pos; [reflexivity | assumption].
assert (0 <= hsqrt y)%Z by (apply Z.lt_le_incl; assumption).
set (ny := r_div (1 + hR y) (2 * (r_sqrt (hR y)))).
set (nz := r_div (1 + r_mult (hR y) (hR z))
             (r_mult (1 + hR z) (r_sqrt (hR y)))).
assert (qy : ny = hR (hdiv (h1 + y)(2 * (hsqrt y)))).
 unfold ny.
 rewrite hdiv_spec, hplus_spec, h1_spec, hscal2_spec, hsqrt_spec; auto.
assert (/2 <= hR z).
 apply Rabs_def2 in cz; destruct (int_z p p1); psatzl R.
assert (0 <= hR z) by psatzl R.
assert (0 <= z)%Z.
 apply hR_pos; assumption.
assert (0 <= h1 + z)%Z.
 apply hR_pos; rewrite hplus_spec, h1_spec; psatzl R.
assert (1 * /4 < (1 + hR z) * r_sqrt (hR y)).
 apply Rmult_le_0_lt_compat; auto; psatzl R.
assert (0 < hmult (h1 + z) (hsqrt y))%Z.
 apply hR_gt_0; rewrite hmult_spec, hplus_spec, h1_spec, hsqrt_spec; auto.
 destruct (r_mult_spec (1 + hR z) (r_sqrt (hR y))); auto; try psatzl R.
assert (qz : nz =
             hR (hdiv (h1 + hmult y z) (hmult (h1 + z) (hsqrt y)))).
 unfold nz.
 rewrite hdiv_spec, hplus_spec, !hmult_spec, hplus_spec, hsqrt_spec, h1_spec;
 auto.
change (hR (hpi_rec (S n) y z prd) =
         rpi_rec r_div r_sqrt r_mult n ny nz
         (r_mult (hR prd) (r_div (1 + ny) (1 + nz)))).
set (ny' := hdiv (h1 + y) (2 * hsqrt y)).
set (nz' := hdiv (h1 + hmult y z) (hmult (h1 + z) (hsqrt y))).
replace (hpi_rec (S n) y z prd) with
       (hpi_rec n ny' nz' (hmult prd (hdiv (h1 + ny') (h1 + nz')))) by reflexivity.
set (npr := r_mult (hR prd) (r_div (1 + ny) (1 + nz))).
assert (4 * (3/2) * INR p * / IZR precision < /100).
 revert smallnp; rewrite plus_INR, Rmult_plus_distr_l,
   (Rmult_plus_distr_r _ _ (/ _)); intros smallnp.
 apply Rle_lt_trans with (2 := smallnp).
 match goal with
  |- (?a <= _)%R => set (x := a);apply Rle_trans with (a + 0)%R;
   unfold x; clear x; try psatzl R
 end.
 apply Rplus_le_compat_l.
 repeat apply Rmult_le_pos; try apply pos_INR; psatzl R.
assert (0 < prd)%Z.
 apply Rabs_def2 in cprd; apply hR_gt_0; psatzl R.
assert (0 <= prd)%Z by (apply Z.lt_le_incl; assumption).
assert (ty := ry_step _ r_div r_sqrt dummy r_div_spec
         r_sqrt_spec p (hR y) p1 cy).
(* TODO : improve the precision. *)
assert (cy' : Rabs (hR y - y_ p (/sqrt 2)) < 2 * / IZR precision) by psatzl R.
assert (tz := rz_step _ r_div r_sqrt r_mult dummy r_mult_spec r_div_spec
         r_sqrt_spec (hR y) (hR z) p p1 cy' cz).
fold ny in ty; fold nz in tz.
assert (/4 * /2 <= hR y * hR z)%R.
 apply Rmult_le_compat; psatzl R.
assert (y_p1p : (1 < y_ (p + 1) (/sqrt 2))%R).
 apply y_gt_1, vs2_bnd.
assert (z_p1p : (1 <= z_ (p + 1) (/sqrt 2))%R).
 apply Rlt_le, z_gt_1;[apply vs2_bnd | lia ].
assert (0 < h1 + nz')%Z.
 apply hR_gt_0; unfold nz'.
 rewrite hplus_spec, <- qz, h1_spec; apply Rabs_def2 in tz; psatzl R.
assert (0 < h1 + ny')%Z.
 apply hR_gt_0; unfold ny'.
 rewrite hplus_spec, <- qy, h1_spec; apply Rabs_def2 in ty; psatzl R.
assert (0  <= hdiv (h1 + ny') (h1 + nz'))%Z.
 apply hdiv_pos;[apply Z.lt_le_incl | ];assumption.
assert (qpr : npr = hR (hmult prd (hdiv (h1 + ny') (h1 + nz')))).
 unfold npr.
 rewrite hmult_spec; auto; rewrite hdiv_spec; auto.
 rewrite !hplus_spec, h1_spec; unfold ny', nz'; rewrite <- qy, <- qz.
 reflexivity.
rewrite qy, qz, qpr; apply (IHn (p + 1)%nat);[ lia | | | | ].
   replace (p + 1 + n)%nat with (p + S n)%nat by ring; assumption.
  rewrite <- qy; exact ty.
 rewrite <- qz; exact tz.
rewrite <- qpr; apply rprod_step; auto.
   exact dummy.
  exact r_mult_spec.
 exact r_div_spec.
exact r_sqrt_spec.
Qed.

Definition hs2 := hsqrt h2.

Lemma hs2_bnd : 141/100 < hR hs2 < 1415/1000.
Proof.
unfold hs2; rewrite hsqrt_spec, h2_spec;[ |apply Z.lt_le_incl, h2_pos].
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; approx_sqrt).
assert (/IZR precision < / 1000).
 apply Rinv_1_lt_contravar; [psatzl R | replace 1000 with (IZR (40 * 25))].
  apply IZR_lt; assumption.
 rewrite mult_IZR; simpl; ring.
destruct (r_sqrt_spec 2); psatzl R.
Qed.

Lemma hss2_bnd : 117/100 < hR (hsqrt hs2) < 119/100.
Proof.
assert (hs2b := hs2_bnd).
assert (1187/1000 < sqrt (hR hs2) < 119/100) by (split; approx_sqrt).
assert (/IZR precision < / 1000).
 apply Rinv_1_lt_contravar; [psatzl R | replace 1000 with (IZR (40 * 25))].
  apply IZR_lt; assumption.
 rewrite mult_IZR; simpl; ring.
rewrite hsqrt_spec;[ | apply hR_pos; psatzl R].
destruct (r_sqrt_spec (hR hs2)); psatzl R.
Qed.

Definition hy1 := hdiv (h1 + hs2) (2 * hsqrt hs2).

Lemma hy1_spec : hR hy1 = ry1 r_div r_sqrt.
Proof.
unfold ry1, hy1, hs2.
assert (t := h2_pos).
assert (t' := Z.lt_le_incl _ _ h2_pos).
destruct hs2_bnd.
assert (0 <= hsqrt h2)%Z.
 apply hR_pos; fold hs2; psatzl R.
destruct hss2_bnd.
assert (0 <= hsqrt hs2)%Z.
 apply hR_pos; psatzl R.
rewrite hdiv_spec, hplus_spec, hscal2_spec, !hsqrt_spec,
    h2_spec, h1_spec; auto.
apply Z.mul_pos_pos;[compute; reflexivity | ].
fold hs2; apply hR_gt_0; psatzl R.
Qed.

Definition hz1 := hsqrt hs2.

Lemma hz1_spec : hR hz1 = rz1 r_sqrt.
assert (t := Z.lt_le_incl _ _ h2_pos).
unfold hz1, hs2; rewrite !hsqrt_spec, h2_spec; auto.
apply hR_pos; fold hs2; destruct hs2_bnd; psatzl R.
Qed.

Definition hpi n :=
  match n with
    O => (h2 + hsqrt h2)%Z
  | S p => hpi_rec p hy1 hz1 (hdiv (h1 + hy1) (h1 + hz1))
  end.

Lemma hpi_rpi : forall n,
  6 * INR n * /IZR precision < / 100 ->
  hR (hpi n) = rpi r_div r_sqrt r_mult n.
intros [ | n] small_e.
 simpl; rewrite hplus_spec, hsqrt_spec, h2_spec.
  reflexivity.
 apply Z.lt_le_incl; exact h2_pos.
assert (1 <= 1)%nat by lia.
assert (4 * (3/2) * S n * / IZR precision</100).
 replace (4 * (3/2)) with 6 by field; assumption.
assert (0 < / IZR precision < / 1000) by exact dummy.
assert (Rabs (hR hy1 - y_ 1 (/sqrt 2)) < 2 * / IZR precision).
 rewrite hy1_spec; apply ry1_correct; auto.
  apply r_div_spec.
 apply r_sqrt_spec.
assert (0 < h1 + hz1)%Z.
 apply Z.add_pos_pos;[apply h1_pos | ].
 change ((0 < hz1)%Z); apply hR_gt_0; rewrite hz1_spec.
 assert (t := rz1_bnd _ _ _ dummy r_div_spec r_sqrt_spec); psatzl R.
assert (Rabs (hR hz1 - z_ 1 (/sqrt 2)) < 4 * / IZR precision).
 rewrite hz1_spec; apply (rz1_correct _ _ _ dummy r_div_spec r_sqrt_spec); auto.
assert (Rabs (hR (hdiv (h1 + hy1) (h1 + hz1)) - pr 1) <
         4 * (3 / 2) * 1%nat * / IZR precision).
 simpl INR; rewrite Rmult_1_r.
 rewrite hdiv_spec, !hplus_spec, hy1_spec, hz1_spec, h1_spec; auto.
 change (r_div (1 + ry1 r_div r_sqrt) (1 + rz1 r_sqrt))
   with (rpi1 r_div r_sqrt).
 apply rpi1_correct;[apply dummy | apply r_div_spec | apply r_sqrt_spec].
simpl; rewrite (hpi_rpi_rec n 1), hdiv_spec, hy1_spec; auto.
unfold rpi1; rewrite !hplus_spec, h1_spec, hy1_spec, hz1_spec.
reflexivity.
Qed.

Require Import Zwf.
Lemma Zpow_Rpower : forall x y, (0 < x) %Z -> (0 <= y)%Z ->
   IZR (x ^ y) = Rpower (IZR x) (IZR y). (* standard *)
Proof.
clear.
intros x y x0; assert (0 < IZR x)%R by (apply (IZR_lt 0); assumption).
induction y as [y IHy] using (well_founded_ind (Zwf_well_founded 0)).
rewrite Z.lt_eq_cases, or_comm; intros [y0 | hgt0].
 now rewrite <- y0; simpl Z.pow; simpl IZR; rewrite Rpower_O.
replace y with (1 + (y - 1))%Z by ring.
rewrite Z.pow_add_r, mult_IZR, plus_IZR, Rpower_plus, Z.pow_1_r; try lia.
rewrite Rpower_1, IHy; auto; unfold Zwf; lia.
Qed.

Lemma hpi_n1 :
  forall n, hpi (n + 1) = hpi_rec n hy1 hz1 (hdiv (h1 + hy1) (h1 + hz1)).
Proof.
intros n; replace (n + 1)%nat with (S n) by ring; reflexivity.
Qed.

Lemma integer_pi :
  forall n, (1 <= n)%nat ->
  600 * INR (n + 1) < IZR precision < Rpower 531 (2 ^ n)/ 14 ->
  Rabs (hR (hpi (n + 1)) - PI)
     < (21 * INR (n + 1) + 3) /IZR precision.
intros n n1; replace (600 * INR (n + 1)) with (6 * INR (n + 1) * 100) by ring.
intros intp.
assert (msp := r_mult_spec).
assert (dsp := r_div_spec).
assert (ssp := r_sqrt_spec).
assert (Rp0 : 0 < IZR precision).
 apply (IZR_lt 0); assumption.
assert (vp0 : 0 < /IZR precision).
 apply Rinv_0_lt_compat; assumption.
replace ((21 * INR (n + 1) + 3) / IZR precision) with
  (/IZR precision + (21 * INR (n + 1) + 2) /IZR precision);
 [|field; apply Rgt_not_eq; assumption].

apply Rlt_trans with
  (agmpi (n + 1) - PI + (21 * INR (n + 1) + 2) * / IZR precision).
 assert (/IZR precision < /1000).
  replace 1000 with (IZR 1000).
   apply Rinv_1_lt_contravar;[apply (IZR_le 1); compute; discriminate | ].
   apply IZR_lt; assumption.
  replace 1000%Z with (40 * 25)%Z by reflexivity.
  rewrite mult_IZR; simpl; ring.
 assert (h2p : (0 <= h2)%Z).
  unfold h2; apply hR_pos; rewrite hscal2_spec.
  apply Rmult_le_pos;[| unfold hR, h1; apply Rmult_le_pos]; psatzl R.
 assert (s2p : (0 < hsqrt h2)%Z).
  assert (141/100 < sqrt 2) by approx_sqrt.
  apply hR_gt_0; rewrite hsqrt_spec, h2_spec; destruct (r_sqrt_spec 2);
   try psatzl R; auto.
 assert (s2nn : (0 <= hsqrt h2)%Z) by apply hsqrt_pos.
 destruct (rz1_bnd (/IZR precision) r_div r_sqrt) as [lz1 uz1];
   [psatzl R | exact r_div_spec | exact r_sqrt_spec | ].
 assert (hpi1_spec : hR (hdiv (h1 + hy1) (h1 + hz1)) = rpi1 r_div r_sqrt).
  unfold rpi1; rewrite hdiv_spec, !hplus_spec, h1_spec, hy1_spec, hz1_spec;
   auto.
  apply hR_gt_0; rewrite hplus_spec, h1_spec, hz1_spec; psatzl R.
 assert (0 < 6 * INR (n + 1)).
  apply Rmult_lt_0_compat;[psatzl R | apply lt_0_INR; lia].
 assert (bp : 6 * INR (n + 1) * / IZR precision < /100).
  apply (Rmult_lt_reg_l (/ (6 * INR (n + 1)))).
   apply Rinv_0_lt_compat; assumption.
   rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;
       [ | apply Rgt_not_eq; assumption].
  rewrite <- Rinv_mult_distr;[|psatzl R|psatzl R].
  apply Rinv_1_lt_contravar.
   assert (1 < INR ( n + 1));[apply lt_1_INR; lia | psatzl R].
  psatzl R.
 rewrite hpi_rpi; auto.
 apply (precision_correct (/IZR precision) r_div r_sqrt r_mult); auto; lia.
repeat apply Rplus_lt_compat_r.
destruct (bound_agmpi n n1) as [_ it]; apply Rle_lt_trans with (1 := it).
clear - Rp0 n1 intp big_precision; unfold agmpi.
assert (1 < sqrt 2 < 15/10) by (split; approx_sqrt).
assert (lp : 0 < 4 * (2 + sqrt 2) < 14) by psatzl R.
match goal with |- ?a < _ => rewrite <- (Rinv_involutive a) end;
 [| apply Rgt_not_eq, Rmult_lt_0_compat;[psatzl R | apply exp_pos]].
apply Rinv_1_lt_contravar.
 apply (IZR_le 1),
 (fun h => Z.le_trans 1 _ _ h (Z.lt_le_incl _ _ big_precision)).
 compute; discriminate.
rewrite Rmult_comm, Rinv_mult_distr;
   try apply Rgt_not_eq;[|apply exp_pos |psatzl R].
rewrite <- Rpower_Ropp, Ropp_involutive.
destruct intp as [_ up]; apply Rlt_trans with (1 := up).
apply Rmult_lt_compat_l;[apply exp_pos | ].
apply Rinv_1_lt_contravar; psatzl R.
Qed.

Lemma Rpower10_4 : Rpower 10 4 = 10000.
replace 4 with (INR 4) by (simpl; ring);
  rewrite Rpower_pow; simpl; [ring|psatzl R].
Qed.

Lemma big5 : forall n, 10 <= n ->  10000 < Rpower 5 n/14.
intros n n10; apply Rmult_lt_reg_r with 14; try psatzl R.
unfold Rdiv; rewrite (Rmult_assoc (Rpower _ _)), Rinv_l, Rmult_1_r;[|psatzl R].
apply Rlt_le_trans with (5 ^ 10);[psatzl R | ].
rewrite <- Rpower_pow;[|psatzl R].
destruct n10 as [d | q];[apply Rlt_le; apply Rpower_lt; simpl;psatzl R | ].
rewrite <- q; apply Req_le; replace (INR 10) with 10 by (simpl; ring); auto.
Qed.

Lemma integer_pi_million :
  IZR precision = Rpower 10 (10 ^ 6 + 4) ->
  (Rabs (hR (hpi 20) - PI) < 6/100 * Rpower 10 (-10 ^ 6))%R.
Proof.
intros precisionq.
assert (nineteen1 : (1 <= 19)%nat) by lia.
assert (precision_10k : 100000 < IZR precision).
 replace 100000 with (10 * 10000) by ring.
 rewrite precisionq, Rpower_plus, Rpower10_4.
 apply Rmult_lt_compat_r;[psatzl R | ].
 pattern 10 at 1; rewrite <- (Rpower_1 10);[ |psatzl R].
 apply Rpower_lt; psatzl R.
assert (prem : 600 * INR (19 + 1) < IZR precision < Rpower 531 (2 ^ 19)/14).
   split; [simpl; psatzl R | rewrite precisionq].
  unfold Rdiv; rewrite <- (exp_ln 14);[ | psatzl R].
  rewrite <- exp_Ropp; unfold Rpower; rewrite <- exp_plus.
  apply exp_increasing, ln_lt_inv;[interval | interval | interval].
apply Rlt_trans with (1 := integer_pi 19 nineteen1 prem).
replace (21 * INR (19 + 1) + 3) with 423 by (simpl; ring).
rewrite precisionq, Rpower_plus; try psatzl R.
unfold Rdiv; rewrite (Rmult_comm (Rpower 10 (10 ^ 6))), Rinv_mult_distr;
  try apply Rgt_not_eq, exp_pos.
assert (0 < / Rpower 10 (10 ^ 6)).
 rewrite <- Rpower_Ropp; apply exp_pos.
rewrite Rpower_Ropp, Rpower10_4; psatzl R.
Qed.

Ltac cmp_pow :=
 match goal with
 | _ => reflexivity
 | |- INR _ = _ => simpl; ring
 | |- _ = INR _ => simpl; ring
 | |- ?a + ?b = ?c + ?d =>
      assert (a = c);[cmp_pow | assert (b = d);[cmp_pow | psatzl R]]
 | |- Rpower ?a ?b = Rpower ?c ?d =>
      let h := fresh "cmppow" in let h' := fresh "cmppow'" in
      assert (h : a = c);[cmp_pow | assert (h' : b = d);
         [ cmp_pow | rewrite h, h'; reflexivity]]
 end.

Lemma integer_pi_ofive :
  IZR precision = Rpower 10 (10 ^ 5 + 4) ->
  (Rabs (hR (hpi 17) - PI) < 5/100 * Rpower 10 (-10 ^ 5))%R.
Proof.
intros precisionq.
assert (sixteen1 : (1 <= 16)%nat) by lia.
assert (precision_10k : 100000 < IZR precision).
 replace 100000 with (10 * 10000) by ring.
 rewrite precisionq, Rpower_plus, Rpower10_4.
 apply Rmult_lt_compat_r;[psatzl R | ].
 pattern 10 at 1; rewrite <- (Rpower_1 10);[ |psatzl R].
 apply Rpower_lt; psatzl R.
assert (prem : 600 * INR (16 + 1) < IZR precision < Rpower 531 (2 ^ 16)/14).
   split; [simpl; psatzl R | rewrite precisionq].
  unfold Rdiv; rewrite <- (exp_ln 14);[ | psatzl R].
  rewrite <- exp_Ropp; unfold Rpower; rewrite <- exp_plus.
  apply exp_increasing, ln_lt_inv;[interval | interval | interval].
apply Rlt_trans with (1 := integer_pi 16 sixteen1 prem).
replace (21 * INR (16 + 1) + 3) with 360 by (simpl; ring).
rewrite precisionq, Rpower_plus; try psatzl R.
unfold Rdiv; rewrite (Rmult_comm (Rpower 10 (10 ^ 5))), Rinv_mult_distr;
  try apply Rgt_not_eq, exp_pos.
assert (0 < / Rpower 10 (10 ^ 5)).
 rewrite <- Rpower_Ropp; apply exp_pos.
rewrite Rpower_Ropp, Rpower10_4; psatzl R.
Qed.

Lemma integer_pi_othree :
  IZR precision = Rpower 10 (10 ^ 3 + 4) ->
  (Rabs (hR (hpi 10) - PI) < 3/100 * Rpower 10 (-10 ^ 3))%R.
Proof.
intros precisionq.
assert (nine1 : (1 <= 9)%nat) by lia.
assert (precision_10k : 10000 < IZR precision).
 replace 10000 with (1 * 10000) by ring.
 rewrite precisionq, Rpower_plus, Rpower10_4.
 apply Rmult_lt_compat_r;[psatzl R | ].
 pattern 1 at 1; rewrite <- (Rpower_O 10);[ |psatzl R].
 apply Rpower_lt; psatzl R.
assert (prem : 600 * INR (9 + 1) < IZR precision < Rpower 531 (2 ^ 9)/14).
   split; [simpl; psatzl R | rewrite precisionq].
  unfold Rdiv; rewrite <- (exp_ln 14);[ | psatzl R].
  rewrite <- exp_Ropp; unfold Rpower; rewrite <- exp_plus.
  apply exp_increasing, ln_lt_inv;[interval | interval | interval].
apply Rlt_trans with (1 := integer_pi 9 nine1 prem).
replace (21 * INR (9 + 1) + 3) with 213 by (simpl; ring).
rewrite precisionq, Rpower_plus; try psatzl R.
unfold Rdiv; rewrite (Rmult_comm (Rpower 10 (10 ^ 3))), Rinv_mult_distr;
  try apply Rgt_not_eq, exp_pos.
assert (0 < / Rpower 10 (10 ^ 3)).
 rewrite <- Rpower_Ropp; apply exp_pos.
rewrite Rpower_Ropp, Rpower10_4; psatzl R.
Qed.

Lemma integer_pi_othree_bin :
  IZR precision = Rpower 2 3336 ->
  (Rabs (hR (hpi 10) - PI))
     < 213 * Rpower 2 (-14) * Rpower 2 (-3322).
Proof.
intros precisionq.
assert (num : 3336 = IZR 3336).
replace 1 with (IZR 1) by reflexivity.
repeat (rewrite <- plus_IZR || rewrite <- mult_IZR); apply f_equal; ring.
assert (nine1 : (1 <= 9)%nat) by lia.
assert (prem : 600 * INR (9 + 1) < IZR precision < Rpower 531 (2 ^ 9)/14).
 split.
  apply Rlt_trans with (Rpower 2 13).
   repeat (rewrite <- Rpower_mult || rewrite Rpower_plus ||
           rewrite Rpower_1); simpl; psatzl R.
   rewrite precisionq; apply Rpower_lt; psatzl R.
 rewrite precisionq.
 apply Rmult_lt_reg_r with 14;[psatzl R | ].
 apply Rlt_trans with (Rpower 2 3336 * Rpower 2 4).
  apply Rmult_lt_compat_l;[apply exp_pos | ].
  repeat (rewrite <- Rpower_mult || rewrite Rpower_plus ||
           rewrite Rpower_1); simpl; psatzl R.
 unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | psatzl R].
 rewrite <- Rpower_plus.
 unfold Rpower; apply exp_increasing; interval.
apply Rlt_le_trans with (1 := integer_pi _ nine1 prem).
replace (21 * INR (9 + 1) + 3) with 213 by (simpl; ring).
rewrite precisionq.
replace 3336 with (14 + 3322) by ring; rewrite Rpower_plus.
unfold Rdiv; rewrite Rinv_mult_distr, <- Rmult_assoc, Rpower_Ropp.
  apply Req_le, f_equal; rewrite Rpower_Ropp; reflexivity.
 apply Rgt_not_eq, exp_pos.
apply Rgt_not_eq, exp_pos.
Qed.

End high_precision.

Lemma rerounding_simple :
  forall k d e l n,
    (0 < d)%Z -> (0 < k)%Z ->
    Rabs (hR (k * d) n - l) < e ->
    (Rh (k * d) e + 1 < n mod d < d - (Rh (k * d) e + 1))%Z ->
    hR k (n / d) < l < hR k ((n / d) + 1).
Proof.
intros k d e l n d0 k0 apx ctr.
assert (ckd : 0 < IZR (k * d)).
 rewrite mult_IZR; apply Rmult_lt_0_compat; apply (IZR_lt 0);
 assumption.
assert (rr : hR k (n / d) = hR (k * d) (d * (n / d))).
 unfold hR. rewrite !mult_IZR.
 rewrite (Rmult_comm (IZR d)); unfold Rdiv.
 rewrite Rmult_assoc, (Rmult_comm (IZR d)).
 rewrite Rinv_mult_distr; try (apply Rgt_not_eq, (IZR_lt 0); assumption).
 rewrite Rmult_assoc, Rinv_l; try (apply Rgt_not_eq, (IZR_lt 0); assumption).
 rewrite Rmult_1_r; reflexivity.
replace (hR k (n / d)) with (hR k (n / d) - hR (k * d) n +
         (hR (k * d) n)) by ring.
split.
 replace l with (-e + (l + e)) by ring.
 apply Rplus_lt_compat;[ | apply Rabs_def2 in apx; psatzl R].
 apply Ropp_lt_cancel; rewrite !Ropp_minus_distr, Ropp_involutive, rr.
 unfold hR, Rdiv.
 rewrite <- Rmult_minus_distr_r.
 rewrite <- minus_IZR.
 rewrite <- Z.mod_eq;[ | apply Z.neq_sym, Z.lt_neq; assumption].
 apply (Rmult_lt_reg_r (IZR (k * d)));[assumption | ].
 rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[|apply Rgt_not_eq; assumption].
 apply Rlt_trans with (hR (k * d) (Rh  (k * d) e + 1) * IZR (k * d)).
  unfold hR, Rdiv; rewrite plus_IZR, Rmult_plus_distr_r.
  replace (IZR (Rh (k * d) e) * / IZR (k * d)) with
  (hR (k * d) (Rh (k * d) e)) by reflexivity.
  replace (IZR 1) with 1 by reflexivity; rewrite Rmult_1_l.
  assert (t := hR_Rh (k * d) (lt_IZR 0 _ ckd) e).
  apply Rmult_lt_compat_r;[assumption | psatzl R].
 unfold hR, Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[|psatzl R].
 apply IZR_lt; destruct ctr as [c1 c2]; assumption.
assert (rr2 : hR k (n / d + 1) = hR k (n / d) + /IZR k).
 unfold hR, Rdiv; rewrite plus_IZR, Rmult_plus_distr_r.
 replace (IZR 1) with 1 by reflexivity; psatzl R.
assert (t := hR_Rh (k * d) (lt_IZR 0 _ ckd) e).
rewrite rr2, rr; apply Rlt_minus_l; clear rr rr2.
apply (Rplus_lt_reg_r (hR (k * d) (n mod d))); rewrite <- hplus_spec.
assert (rr3 : hR (k * d) (d * (n / d) + n mod d) = hR (k * d) n).
 unfold hR; rewrite <- Z.div_mod; [reflexivity | ].
 apply Z.neq_sym, Z.lt_neq; assumption.
rewrite rr3.
apply Rlt_trans with (l - e);[|apply Rabs_def2 in apx; psatzl R].
unfold Rminus; rewrite Rplus_assoc; apply Rplus_lt_compat_l.
rewrite Rplus_comm; apply  (proj2 (Rlt_minus_l _ _ _)).
assert (sk : /IZR k * IZR (k * d) = IZR d).
 rewrite mult_IZR, <- Rmult_assoc, Rinv_l, Rmult_1_l.
  reflexivity.
 apply Rgt_not_eq, (IZR_lt 0); assumption.
apply (Rmult_lt_reg_r (IZR (k * d))); [psatzl R | unfold hR, Rdiv].
rewrite Rmult_plus_distr_r, sk, Rmult_assoc, Rinv_l, Rmult_1_r;[|psatzl R].
apply Rlt_trans with (-(hR (k * d) ((Rh (k * d) e) + 1)) * IZR(k * d) + IZR d).
 unfold hR, Rdiv.
 rewrite Ropp_mult_distr_l_reverse, Rmult_assoc, Rinv_l, Rmult_1_r;[ |psatzl R].
 rewrite <-opp_IZR, <- plus_IZR; apply IZR_lt.
 rewrite Z.add_comm, Z.add_opp_r; destruct ctr as [c1 c2]; assumption.
apply Rplus_lt_compat_r.
rewrite !Ropp_mult_distr_l_reverse; apply Ropp_lt_contravar, Rmult_lt_compat_r;
 [assumption | ].
rewrite hplus_spec; unfold hR at 2; simpl IZR; psatzl R.
Qed.

Lemma pi_million :
  let precision := (10 ^ (10 ^ 6 + 4))%Z in
  let n := hpi precision 20 in
      (601 < n mod 10000 < 9399)%Z ->
  let n' := (n/10000)%Z in
   0 < PI - hR (10 ^ (10 ^ 6)) n' < Rpower 10 (- 10 ^ 6).
Proof.
intros pr n ctr n'.
assert (main : hR (10 ^ (10 ^ 6)) n' < PI < hR (10 ^ (10 ^ 6)) (n' + 1)).
 assert (cd : (0 < 10 ^ 4)%Z) by (compute; reflexivity).
 assert (cp : (0 < 10 ^ (10 ^ 6))%Z).
  apply Z.pow_pos_nonneg; [reflexivity | compute; discriminate].
 assert (t':Rabs (hR (10 ^ (10 ^ 6) * 10 ^ 4) n - PI)
                < 6/100 * Rpower 10 (- 10 ^ 6)).
  assert (powm : hR (10 ^ (10 ^ 6) * 10 ^ 4) n = hR (10 ^ (10 ^ 6 + 4)) n).
   unfold hR; rewrite Z.pow_add_r;[reflexivity | | ]; compute; discriminate.
  rewrite powm.
  assert (gt1000 : (1000 < 10 ^ (10 ^ 6 + 4))%Z).
   assert (st : (1000 = 1 ^ (10 ^ 6) * 1000)%Z).
    rewrite Z.pow_1_l, Z.mul_1_l;[reflexivity | ].
    apply Z.pow_nonneg;compute; discriminate.
   rewrite st, Z.pow_add_r;[ | compute; discriminate | compute; discriminate].
   apply Z.mul_lt_mono_nonneg.
      apply Z.pow_nonneg; compute; discriminate.
     apply Z.pow_lt_mono_l;[reflexivity | compute; split;[discriminate | reflexivity]].
    compute; discriminate.
   compute; reflexivity.
  assert (cp' : (0 < 10 ^ (10 ^ 6 + 4))%Z).
   apply Z.pow_pos_nonneg; [reflexivity | compute; discriminate].
  assert (q : IZR (10 ^ (10 ^ 6 + 4)) = Rpower 10 (10 ^ 6 + 4)).
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 10) with 10 by (simpl; ring).
   apply f_equal; rewrite plus_IZR.
   change 6%Z with (Z.of_nat 6).
   rewrite <- pow_IZR.
   replace (IZR 10) with 10 by (simpl; ring).
   replace (IZR 4) with 4 by (simpl; ring).
   reflexivity.
  apply (integer_pi_million (10 ^ (10 ^ 6 + 4)) gt1000 cp' q).
 assert (ctr' : (Rh (10 ^ 10 ^ 6 * 10 ^ 4)
                   (6 / 100 * Rpower 10 (- 10 ^ 6)) + 1 <
                  n mod 10 ^ 4 <
                   10 ^ 4 - (Rh (10 ^ 10 ^ 6 * 10 ^ 4)
                   (6/ 100 * Rpower 10 (- 10 ^ 6)) + 1))%Z).
 assert (sm: (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (6/ 100 * Rpower 10 (- 10 ^ 6)) = 600)%Z).
   unfold Rh; rewrite mult_IZR.
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 10) with 10 by (simpl; ring).
   replace (IZR 6) with (INR 6) by (simpl; ring).
   rewrite Rpower_pow, !Rmult_assoc, (Rmult_comm (6/100)),
      <- Rmult_assoc;[ | psatzl R].
   rewrite <- Rpower_plus, Rplus_opp_l, Rpower_O, Rmult_1_l;[ | psatzl R].
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 4) with (INR 4) by (simpl; ring).
   replace (IZR 10) with 10 by (simpl; ring).
   rewrite Rpower_pow;[ | psatzl R].
   replace (10 ^ 4 * (6 / 100)) with (IZR 20 * IZR 30) by (simpl; psatzl R).
   unfold RbZ; rewrite <- mult_IZR, floor_IZR; reflexivity.
  rewrite sm.
  assert (s10m' : (10 ^ 4 = 10000)%Z) by ring.
  assert (s10m : (forall x, x  mod 10 ^ 4 = x mod 10000)%Z).
   clear; assert (s10m : (10 ^ 4 = 10000)%Z) by ring.
   intros x; rewrite !Z.mod_eq, s10m;
   [reflexivity | compute; discriminate | compute; discriminate].
  rewrite s10m, s10m'.
  assumption.
 assert (t := rerounding_simple (10 ^ (10 ^ 6)) (10 ^ 4) (6/100 * Rpower 10 (-10 ^ 6))
             PI n cd cp t' ctr').
 exact t.
split;[apply Rlt_Rminus; tauto | destruct main as [_ main]]; revert main.
rewrite hplus_spec; unfold hR at 2; simpl (IZR 1).
unfold Rdiv; rewrite Rmult_1_l.
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
replace (IZR 10) with 10 by (simpl; field).
replace (IZR 6) with (INR 6) by (simpl; field).
rewrite Rpower_pow;[|psatzl R].
rewrite Rpower_Ropp; psatzl R.
Qed.

Lemma pi_ofive :
  let precision := (10 ^ (10 ^ 5 + 4))%Z in
  let n := hpi precision 17 in
      (501 < n mod 10000 < 9499)%Z ->
  let n' := (n/10000)%Z in
   0 < PI - hR (10 ^ (10 ^ 5)) n' < Rpower 10 (- 10 ^ 5).
Proof.
intros pr n ctr n'.
assert (main : hR (10 ^ (10 ^ 5)) n' < PI < hR (10 ^ (10 ^ 5)) (n' + 1)).
 assert (cd : (0 < 10 ^ 4)%Z) by (compute; reflexivity).
 assert (cp : (0 < 10 ^ (10 ^ 5))%Z).
  apply Z.pow_pos_nonneg; [reflexivity | compute; discriminate].
 assert (t':Rabs (hR (10 ^ (10 ^ 5) * 10 ^ 4) n - PI) < 5/100 * Rpower 10 (- 10 ^ 5)).
  assert (powm : hR (10 ^ (10 ^ 5) * 10 ^ 4) n = hR (10 ^ (10 ^ 5 + 4)) n).
   unfold hR; rewrite Z.pow_add_r;[reflexivity | | ]; compute; discriminate.
  rewrite powm.
  assert (gt1000 : (1000 < 10 ^ (10 ^ 5 + 4))%Z).
   assert (st : (1000 = 1 ^ (10 ^ 5) * 1000)%Z).
    rewrite Z.pow_1_l, Z.mul_1_l;[reflexivity | ].
    apply Z.pow_nonneg;compute; discriminate.
   rewrite st, Z.pow_add_r;[ | compute; discriminate | compute; discriminate].
   apply Z.mul_lt_mono_nonneg.
      apply Z.pow_nonneg; compute; discriminate.
     apply Z.pow_lt_mono_l;[reflexivity | compute; split;[discriminate | reflexivity]].
    compute; discriminate.
   compute; reflexivity.
  assert (cp' : (0 < 10 ^ (10 ^ 5 + 4))%Z).
    apply Z.pow_pos_nonneg;
    [reflexivity | compute; discriminate].
(* funny : a bug by the user here, (replacing 5 by 6), causes a time costly computation. *)
  assert (q : IZR (10 ^ (10 ^ 5 + 4)) = Rpower 10  (10 ^ 5 + 4)).
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 10) with 10 by (simpl; ring).
   apply f_equal; rewrite plus_IZR.
   change 5%Z with (Z.of_nat 5).
   rewrite <- pow_IZR.
   replace (IZR 10) with 10 by (simpl; ring).
   replace (IZR 4) with 4 by (simpl; ring).
   reflexivity.
  apply (integer_pi_ofive (10 ^ (10 ^ 5 + 4)) gt1000 cp' q).
assert (ctr' : (Rh (10 ^ 10 ^ 5 * 10 ^ 4) (5/ 100 * Rpower 10 (- 10 ^ 5)) + 1 <
       n mod 10 ^ 4 <
       10 ^ 4 - (Rh (10 ^ 10 ^ 5 * 10 ^ 4) (5/ 100 * Rpower 10 (- 10 ^ 5)) + 1))%Z).
 assert (sm: (Rh (10 ^ 10 ^ 5 * 10 ^ 4) (5/ 100 * Rpower 10 (- 10 ^ 5)) = 500)%Z).
   unfold Rh; rewrite mult_IZR.
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 10) with 10 by (simpl; ring).
   replace (IZR 5) with (INR 5) by (simpl; ring).
   rewrite Rpower_pow, !Rmult_assoc, (Rmult_comm (5/100)), <- Rmult_assoc;
     [ | psatzl R].
   rewrite <- Rpower_plus, Rplus_opp_l, Rpower_O, Rmult_1_l;[ | psatzl R].
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 4) with (INR 4) by (simpl; ring).
   replace (IZR 10) with 10 by (simpl; field).
   rewrite Rpower_pow;[ | psatzl R].
   replace (10 ^ 4 * (5/100)) with (IZR 500) by (simpl; psatzl R).
   unfold RbZ; rewrite floor_IZR; reflexivity.
  rewrite sm.
  assumption.
 exact (rerounding_simple (10 ^ (10 ^ 5)) (10 ^ 4) _
             PI n cd cp t' ctr').
split;[apply Rlt_Rminus; tauto | destruct main as [_ main]]; revert main.
rewrite hplus_spec; unfold hR at 2; simpl (IZR 1); unfold Rdiv; rewrite Rmult_1_l.
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
replace (IZR 10) with 10 by (simpl; field).
replace (IZR 5) with (INR 5) by (simpl; field).
rewrite Rpower_pow;[|psatzl R].
rewrite Rpower_Ropp; psatzl R.
Qed.

(* One could probably restrict the number of extra required bits
  to be only 8 or 9, as this would be enough to do better than 213 *)
Lemma pi_othree_bin :
  let precision := (2 ^ 3336)%Z in
  let n := hpi precision 10 in
      (214 < n mod 16384 < 16170)%Z ->
  let n' := (n/2 ^ 14)%Z in
   0 < PI - hR (2 ^ 3322) n' < Rpower 2 (- 3322).
Proof.
intros pr n ctr n'.
assert (main : hR (2 ^ 3322) n' < PI < hR (2 ^ 3322) (n' + 1)).
 assert (cd : (0 < 2 ^ 14)%Z) by (compute; reflexivity).
 assert (cp : (0 < 2 ^ 3322)%Z).
  apply Z.pow_pos_nonneg;
    [reflexivity | compute; discriminate].
 assert (t':Rabs (hR (2 ^ 3322 * 2 ^ 14) n - PI) < 213 * Rpower 2 (- 14) *
              Rpower 2 (-3322)).
  assert (powm : hR (2 ^ 3322 * 2 ^ 14) n = hR (2 ^ 3336) n).
   unfold hR; rewrite <- Z.pow_add_r;
     [reflexivity | | ]; compute; discriminate.
  rewrite powm.
  assert (gt1000 : (1000 < 2 ^ 3336)%Z).
   apply Z.lt_trans with ((2 ^ 10)%Z).
    reflexivity.
   apply Z.pow_lt_mono_r;
     [ | rewrite <- Z.leb_le | ]; reflexivity.
(* In other proofs, this is done by direct computations. *)
  assert (cp' : (0 < 2 ^ 3336)%Z).
   apply Z.pow_pos_nonneg; [reflexivity | compute; discriminate].
  assert (q : IZR (2 ^ 3336)%Z = Rpower 2 3336).
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 2) with 2 by reflexivity.
   apply f_equal.
   change (3336%Z) with (3 * 11 * 20 * 5 + 4 * 9)%Z.
   rewrite !plus_IZR, !mult_IZR; simpl; ring.
  apply (integer_pi_othree_bin _ gt1000 cp' q).
 assert (ctr' : (Rh (2 ^ 3322 * 2 ^ 14)
                  (213 * Rpower 2 (-14) * Rpower 2 (-3322)) + 1 <
       n mod 2 ^ 14 <
       2 ^ 14 - (Rh (2 ^ 3322 * 2 ^ 14)
             (213 * Rpower 2 (-14) * Rpower 2 (-3322)) + 1))%Z).
 assert (sm: (Rh (2 ^ 3322 * 2 ^ 14) (213 * Rpower 2 (-14) * Rpower 2 (-3322)) = 213)%Z).
   unfold Rh; rewrite mult_IZR.
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
   replace (IZR 2) with 2 by (simpl; ring).
   rewrite !Rmult_assoc, <- !Rpower_plus.
   replace (IZR 3322) with
     (IZR (3 * 11 * 5 * 20 + 22)) by (apply f_equal; reflexivity).
   rewrite plus_IZR, !mult_IZR; simpl.
   match goal with |- (RbZ (_ * Rpower _ ?x) = _)%Z =>
     assert (x0 : x = 0); [ring | rewrite x0, Rpower_O, Rmult_1_r;
                 [  | psatzl R]]
   end.
   replace 213 with (IZR 10 * IZR 20 + IZR 13) by (simpl; ring).
   rewrite <- !mult_IZR, <- !plus_IZR.
   unfold RbZ; rewrite floor_IZR; reflexivity.
  rewrite sm.
  assumption.
 exact (rerounding_simple (2 ^ 3322) (2 ^ 14) _
             PI n cd cp t' ctr').
split;[apply Rlt_Rminus; tauto | destruct main as [_ main]]; revert main.
rewrite hplus_spec; unfold hR at 2; simpl (IZR 1); unfold Rdiv; rewrite Rmult_1_l.
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
rewrite <- Rpower_Ropp; replace (IZR 2) with 2 by reflexivity.
replace (IZR 3322) with 3322;[psatzl R | ].
replace (3322%Z) with (3 * 11 * 10 * 10 + 22)%Z by reflexivity.
rewrite plus_IZR, !mult_IZR; simpl; ring.
Qed.

Lemma change_precision : forall p1 p2 x, (0 < p1)%Z ->
  (p1 < p2)%Z ->
  hR p2 x- /IZR p1 < hR p1 (x * p1/p2) <= hR p2 x.
Proof.
intros p1 p2 x p0 cmpp.
assert (0 < p2)%Z by (apply Z.lt_trans with (1 := p0) (2 :=cmpp)).
unfold hR; split.
 apply Rmult_lt_reg_r with (IZR p1); [apply (IZR_lt 0); assumption | ].
 rewrite Rmult_minus_distr_r.
 unfold Rdiv at 2; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
  [|apply Rgt_not_eq, (IZR_lt 0); assumption].
 apply Rmult_lt_reg_r with (IZR p2); [apply (IZR_lt 0); assumption | ].
 rewrite Rmult_minus_distr_r, Rmult_1_l.
 unfold Rdiv; rewrite !Rmult_assoc, (Rmult_comm (/ _)), !Rmult_assoc.
 rewrite Rinv_r, Rmult_1_r;[ | apply Rgt_not_eq, (IZR_lt 0); assumption].
 assert (help : forall x y z, x < z + y -> x - y < z) by (intros; psatzl R).
 apply help; clear help; rewrite <- !mult_IZR,  <- plus_IZR;  apply IZR_lt.
 pattern (x * p1)%Z at 1; rewrite (Z_div_mod_eq (x * p1)  (p2));
  [|apply Zlt_gt; assumption].
 rewrite (Zmult_comm (p2)).
 apply Zplus_lt_compat_l.
 destruct (Zmod_pos_bound (x * p1) (p2)); assumption.
apply Rmult_le_reg_r with (IZR p1); [apply (IZR_lt 0); assumption | ].
 unfold Rdiv at 1; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
  [|apply Rgt_not_eq, (IZR_lt 0); assumption].
apply Rmult_le_reg_r with (IZR p2); [apply (IZR_lt 0); assumption | ].
unfold Rdiv; rewrite !Rmult_assoc, (Rmult_comm (/ _)), !Rmult_assoc.
 rewrite Rinv_r, Rmult_1_r;[ | apply Rgt_not_eq, (IZR_lt 0); assumption].
rewrite <- !mult_IZR;  apply IZR_le.
rewrite Zmult_comm; apply Z.mul_div_le; assumption.
Qed.

(*  When the error ratio was 29, we used
    361 = (29*10+3) *10^4/2^13 + 3 (rounded above)
    Now that the error ration is 21, we use
    264 = (21 * 10 + 3) * 10^4/2^13 + 3 (rounded above, too) *)
Lemma pi_othree :
  let precision := (2 ^ 3336)%Z in
  let n := hpi precision 10 in
    let n' := (n * 10 ^ (10 ^ 3 + 4) / 2 ^ 3336)%Z in
      (265 < n' mod 10 ^ 4 < 9735)%Z ->
   0 < PI - hR (10 ^ (10 ^ 3)) (n' / 10 ^ 4) < Rpower 10 (-(Rpower 10 3)).
assert (helpring : forall b a c:R, a - c = a - b + (b - c))
          by (intros; ring).
assert (gt1000 : (1000 < 2 ^ 3336)%Z)
   by (rewrite <- Z.ltb_lt; reflexivity).
assert (p0 : (0 < 2 ^ 3336)%Z) by (rewrite <- Z.ltb_lt; reflexivity).
assert (q : IZR (2 ^ 3336) = Rpower 2 3336).
 rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
 replace (IZR 2) with 2 by reflexivity.
 apply f_equal.
 change (3336%Z) with (3 * 11 * 20 * 5 + 4 * 9)%Z.
 rewrite plus_IZR, !mult_IZR; simpl; ring.
assert (t := integer_pi_othree_bin (2 ^ 3336) gt1000 p0 q).
intros precision n n' ctr; fold precision in q, t.
(* fold or change did not manage to avoid heavy computation here *)
assert (t' :
 Rabs (hR precision n - PI) < 213 * Rpower 2 (-14) * Rpower 2 (-3322))
 by exact t; clear t.
assert (p20 : (0 < 10 ^ (10 ^ 3 + 4))%Z).
 apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
assert (cmpp : (10 ^ (10 ^ 3 + 4) < 2 ^ 3336)%Z).
 rewrite <- Z.ltb_lt; vm_compute; reflexivity.
assert (t := change_precision _ (2 ^ 3336) n p20 cmpp).
fold precision in t.
(* again, fold n' does not work here *)
assert (t'' :
   hR precision n - / IZR (10 ^ (10 ^ 3 + 4)) <
   hR (10 ^ (10 ^ 3 + 4)) n' <= hR precision n) by exact t; clear t.
(* This does not work either
replace (n * 10 ^ (10 ^ 3 + 4) / precision)%Z with
  n' in t;[ | unfold n', precision].
*)
assert (k0 : (0 < 10 ^ (10 ^ 3))%Z) by
    (rewrite <- Z.ltb_lt; vm_compute; reflexivity).
assert (d0 : (0 < 10 ^ 4)%Z) by
    (rewrite <- Z.ltb_lt; vm_compute; reflexivity).
assert (pwr : (10 ^ (10 ^ 3 + 4))%Z = (10 ^ 10 ^ 3 * 10 ^ 4)%Z).
  rewrite <- Z.pow_add_r;[reflexivity | | ]; compute; discriminate.
(* BUG? : strange behavior: I can't use replace here because it
   performs too much computation. but this does not happen if pwr does
   not exist. *)
assert (pwr2 : hR (10 ^ 10 ^ 3 * 10 ^ 4) n' = hR (10 ^ (10 ^ 3 + 4)) n').
     (unfold hR; rewrite pwr; reflexivity).
assert (n'cl : Rabs (hR (10 ^ 10 ^ 3 * (10 ^ 4)) n' - PI) <
            264 * /IZR (10 ^ (10 ^ 3) * 10 ^ 4)%Z).
 rewrite pwr2, <- pwr.
 assert (exists v, v = hR (10 ^ (10 ^ 3 + 4)) n') as [v hv].
  eapply ex_intro; eapply refl_equal.
 assert (exists vp, vp = precision) as [vp hvp].
  eapply ex_intro; eapply refl_equal.
 rewrite <- hv.
 (* BUG: I can't do this
 replace (v - PI) with
  ((v - hR vp n) + (hR vp n - PI)) by ring. *)
  rewrite (helpring (hR precision n)).
 apply Rle_lt_trans with (1 := Rabs_triang _ _).
 apply Rlt_trans with (/IZR (10 ^ (10 ^ 3 + 4)) +
                    213 * Rpower 2 (-14) * Rpower 2 (-3322)).
  apply Rplus_lt_compat.
   assert (0 < / IZR (10 ^ (10 ^ 3 + 4))).
    apply Rinv_0_lt_compat, (IZR_lt 0); vm_compute; reflexivity.
   apply Rabs_def1.
  (* BUG? : I don't understand why psatzl R can't do this one *)
    apply Rle_lt_trans with 0;[ | psatzl R].
    rewrite hv; apply Rle_minus; destruct t'' as [_ it]; exact it.
   apply Rplus_lt_reg_r with (hR precision n).
   unfold Rminus; rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
   rewrite hv; rewrite Rplus_comm; destruct t'' as [it _]; exact it.
  exact t'.
 assert (num : 3322 = IZR 3322).
  change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
  reflexivity.
 assert (num14 : 14 = IZR 14).
  change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
  reflexivity.
 assert (num213 : 213 = IZR 213).
  change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
  reflexivity.
 assert (num264 : 264 = IZR 264).
  change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
  reflexivity.
 rewrite num, num213, num264, num14.
 change 2 with (IZR 2).
 assert (0 < IZR (10 ^ (10 ^ 3 + 4))).
  apply (IZR_lt 0); apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
 apply Rmult_lt_reg_r with (IZR (10 ^ (10 ^ 3 + 4))).
  assumption.
(* Bug? here, I can't finish the rewriting wit Rmult_1_r *)
 rewrite Rmult_plus_distr_r, 3!Rmult_assoc, Rinv_l;
  [ | apply Rgt_not_eq; assumption].
 (* I have to set the instantiation precisely! *)
 rewrite (Rmult_1_r (IZR 264)).
 rewrite (Rmult_comm (Rpower (IZR 2) (-IZR 3322))
           (IZR (10 ^ (10 ^ 3 + 4)))).
 rewrite (Rmult_comm (Rpower (IZR 2) (-IZR 14))).
 rewrite <- 2!Rmult_assoc.
 apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR 14)).
  apply exp_pos.
 rewrite Rmult_plus_distr_r, !Rmult_assoc, <- Rpower_plus, Rplus_opp_l.
 rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
 apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR 3322)).
  apply exp_pos.
 rewrite Rmult_plus_distr_r, !Rmult_assoc, <- !Rpower_plus, Rplus_opp_l.
 rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
 rewrite <- !plus_IZR, <- Zpow_Rpower;
  [ | reflexivity | vm_compute; discriminate ].
 rewrite Rmult_1_l, <- !mult_IZR.
 rewrite <- plus_IZR.
 apply IZR_lt.
 change (2 ^ (14 + 3322) + (213 * 10 ^ (10 ^ 3 + 4)) <
    264 * 2 ^ (14 + 3322))%Z.
 rewrite <- Z.ltb_lt; vm_compute; reflexivity.
assert (ctr' :
 (Rh (10 ^ 10 ^ 3 * 10 ^ 4) (264 * / IZR (10 ^ 10 ^ 3 * 10 ^ 4)) + 1 <
       n' mod 10 ^ 4 <
       10 ^ 4 -
       (Rh (10 ^ 10 ^ 3 * 10 ^ 4) (264 * / IZR (10 ^ 10 ^ 3 * 10 ^ 4)) + 1))%Z).
 assert (sm: (Rh (10 ^ 10 ^ 3 * 10 ^ 4) (264 * /IZR (10 ^ 10 ^ 3 * 10 ^ 4))
               = 264)%Z).
  unfold Rh; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
   [ | apply Rgt_not_eq, (IZR_lt 0); vm_compute; reflexivity].
 assert (num264 : 264 = IZR 264).
  change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
  reflexivity.
  unfold RbZ; rewrite num264, floor_IZR; reflexivity.
 rewrite sm; assumption.
 destruct (rerounding_simple (10 ^ 10 ^ 3) (10 ^ 4)
          (264 * /IZR (10 ^ (10 ^ 3) * 10 ^ 4)) PI n' d0 k0 n'cl ctr')
   as [rrs1 rrs2].
split.
 (* psatzl does not do this one *)
 apply Rlt_Rminus; assumption.
revert rrs2; unfold hR, Rdiv; rewrite plus_IZR.
rewrite Rmult_plus_distr_r; intros rrs2.
rewrite Rlt_minus_l; apply Rlt_le_trans with (1 := rrs2).
rewrite Rplus_comm; apply Rplus_le_compat_r.
apply Req_le; clear.
change (IZR 1) with 1; rewrite Rmult_1_l, Rpower_Ropp.
replace 10 with (IZR 10) by (simpl; ring).
replace 3 with (IZR 3) by (simpl; ring).
rewrite <- Zpow_Rpower;[ | reflexivity | compute; discriminate].
rewrite <- Zpow_Rpower;[ | reflexivity | compute; discriminate].
reflexivity.
Qed.

Lemma pow10million_pow2 : (10 ^ (10 ^ 6 + 4) < 2 ^ 3321942)%Z.
Proof.
apply lt_IZR.
rewrite !Zpow_Rpower;[ | reflexivity | discriminate | reflexivity | discriminate ].
rewrite plus_IZR, Zpow_Rpower;[ | reflexivity | discriminate].
replace (IZR (3321942)) with 3321942; cycle 1.
  replace (3321942)%Z with (42 + 100 * (19 + 100 * (32 + 100 * 3)))%Z
    by reflexivity.
  now repeat (rewrite  plus_IZR || rewrite mult_IZR); simpl; psatzl R.
simpl; unfold Rpower; apply exp_increasing; interval.
Qed.

Require Import Bool.

Definition million_digit_pi : bool * Z :=
  let precision := (2 ^ 3321942)%Z in
  let n := hpi precision 20 in
    let n' := (n * 10 ^ (10 ^ 6 + 4) / 2 ^ 3321942)%Z in
    let (q, r) := Z.div_eucl n' (10 ^ 4) in
    ((427 <? r)%Z && (r <? 9573)%Z, q).

Ltac decompose_big_number_r n :=
  match n with
    | (?p * 10 ^ ?c + ?r)%Z =>
       let b := eval compute in (Z.ltb 9 p) in
       match b with
         true =>
         let v := eval compute in (Z.div_eucl p 10) in
         let p' := eval compute in (fst v) in
         let d  := eval compute in (snd v) in
         let c' := eval compute in (c + 1)%Z in
         decompose_big_number_r (p' * 10 ^ c' + (d * 10 ^ c + r))%Z
       | false => n
       end
  end.

Ltac decompose_big_number n :=
  let b := eval compute in (Z.ltb 9 n) in
  match b with
    true =>
    let v := eval compute in (Z.div_eucl n 10) in
    let p' := eval compute in (fst v) in
    let d  := eval compute in (snd v) in
    decompose_big_number_r (p' * 10 ^ 1 + d)%Z
  | false => n
  end.

(* An example of usage for decompose_number, but the
time information says between 2 and 4 seconds
 (that comment about timing is not valid anymore,
 maybe that was when the type was BigZ) *)
Lemma toto : (332233 = 33 * 10 ^ 4 + 22 * 10 ^ 2 + 33)%Z.
match goal with |- (?x = _)%Z =>
   let u := constr:(x * 10 ^ 0 + 0)%Z in
   let v := decompose_big_number u in
   assert (x = v)%Z
end.
ring.
rewrite H; ring.
Qed.

Ltac R_to_Z n :=
  match n with
   | 1 => constr:(1%Z)
   | (1 + ?x) => let v1 := R_to_Z x in
     let w := constr:(Z.add 1 v1) in
     let w' := eval compute in w in w'
   | (1 + 1) * ?x => let v1 := R_to_Z x in
     let w := constr:(Z.mul 2 v1) in
     let w' := eval compute in w in w'
  end.

(* A tactic that generates a real number in the right
 pattern for the display machinery. *)
Ltac Z_to_R n :=
let b1 := eval compute in (Z.eqb n 1)%Z in
match b1 with
  true => constr:(1%R)
| false =>
  let b2 := eval compute in (Z.eqb n 2)%Z in
  match b2 with
    true => constr:(2%R)
  | false => let b3 := eval compute in (Z.eqb n 3)%Z in
    match b3 with
      true => constr:(3%R)
    | false =>
      let b := eval compute in (Z.ltb 0 n) in
      match b with
        false => 0
      | true => let b' := eval compute in (Z.odd n) in
        let r := eval compute in (Z.div n 2) in
        let rv := Z_to_R r in
        let drv := constr:(2 * rv)%R in
        match b' with
          true => constr:(1 + drv)%R
        | false => constr:drv
        end
      end
    end
  end
end.

Lemma million_digit_lb_bin : (2 ^ 3321942 < 2 * 10 ^ (10 ^ 6 + 4))%Z.
Proof.
apply lt_IZR.
rewrite mult_IZR.
rewrite !Zpow_Rpower;[ | reflexivity | discriminate | reflexivity | discriminate ].
rewrite plus_IZR, Zpow_Rpower;[ | reflexivity | discriminate].
replace (IZR (3321942)) with 3321942; cycle 1.
  replace (3321942)%Z with (42 + 100 * (19 + 100 * (32 + 100 * 3)))%Z
    by reflexivity.
  now repeat (rewrite  plus_IZR || rewrite mult_IZR); simpl; psatzl R.
pattern (IZR 2) at 2; rewrite <- (exp_ln (IZR 2)); simpl (IZR 2);[ | psatzl R].
unfold Rpower.
rewrite <- exp_plus; apply exp_increasing; simpl; interval.
Qed.

Lemma pi_osix :
  fst million_digit_pi = true ->
    hR (10 ^ (10 ^ 6)) (snd million_digit_pi) < PI <
    hR (10 ^ (10 ^ 6)) (snd million_digit_pi) + Rpower 10 (-(Rpower 10 6)).
Proof.
assert (num14 : 14 = IZR 14) by (compute; ring).
assert (num2 : 2 = IZR 2) by (compute; ring).
assert (main : fst million_digit_pi = true ->
         0 < PI - hR (10 ^ (10 ^ 6)) (snd million_digit_pi) <
           Rpower 10 (-(Rpower 10 6)));
  [| intros ft; apply main in ft; clear main; psatzl R].
match type of pow10million_pow2 with
  (Z.lt _  (Z.pow _ ?v)) => set (prec := v)
end.
let v := eval compute in (prec - 14)%Z in set (prec' := v).
assert
  (main : let precision := (2 ^ prec)%Z in
  let n := hpi precision 20 in
    let n' := (n * 10 ^ (10 ^ 6 + 4) / 2 ^ prec)%Z in
    ((427 <? n' mod 10 ^ 4)%Z && (n' mod 10 ^ 4 <? 9573)%Z = true) ->
   0 < PI - hR (10 ^ (10 ^ 6)) (n' / 10 ^ 4) < Rpower 10 (-(Rpower 10 6))).
 let v := decompose_big_number prec' in set (u := v).
 let v := eval compute in (Z.eqb u 1)%Z in set (b1 := v).
 let v := Z_to_R prec in set (precr := v).
 let v := Z_to_R prec' in set (prec'r := v).
 assert (qb' : prec'r = IZR u).
  unfold prec'r, u; repeat (rewrite mult_IZR || rewrite plus_IZR).
 repeat (match goal with
    |- context[IZR (Zpos ?x)] =>
       let v := constr:(Zpos x) in
       let v1 := Z_to_R v in
       replace (IZR (Zpos x)) with v1 by (simpl; ring)
    | |- context[IZR (_ ^ ?x)] => let v := eval compute in (Zabs_nat x) in
         change x with (Z.of_nat v)
    end; rewrite <- ? pow_IZR
    ); ring.
 let v := eval compute in (prec - prec')%Z in set (u' := v).
 assert (qb : precr = IZR (u + u')).
  unfold precr, u, u'; repeat (rewrite mult_IZR || rewrite plus_IZR).
  repeat (match goal with
    |- context[IZR (Zpos ?x)] =>
       let v := eval compute in (IZR (Zpos x)) in
       change (IZR (Zpos x)) with v
    | |- context [IZR (_ ^ ?x)] =>
       let v := eval compute in (Z.abs_nat x) in
       change x with (Z.of_nat v)
    end; rewrite <- ? pow_IZR); ring.
 assert (helpring : forall b a c:R, a - c = a - b + (b - c))
          by (intros; ring).
 assert (gt1000 : (1000 < 2 ^ prec)%Z).
  change 1000%Z with (1000 * 1)%Z.
  change prec with (10 + (prec - 10))%Z.
  rewrite Z.pow_add_r;[ | compute | compute ]; try discriminate.
  apply Z.mul_lt_mono_nonneg;[discriminate | reflexivity | discriminate| ].
  rewrite <- Z.pow_gt_1;[ reflexivity | reflexivity].
 assert (p0 : (0 < 2 ^ prec)%Z).
  apply Z.pow_pos_nonneg;[reflexivity | discriminate].
 assert (q : IZR (2 ^ prec) = Rpower 2 precr).
  rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
  replace (IZR 2) with 2 by reflexivity.
  apply f_equal; rewrite qb; apply f_equal; reflexivity.
 intros precision n n'.
 assert (nineteen1 : (1 <= 19)%nat) by lia.
 assert (t' : 600 * INR 20 < IZR precision < Rpower 531 (2 ^ 19) / 14).
  split.
(* This does not work, probably because 3321929 does not seem to parse,
   even as an integer.
  replace precision with ((2 ^ 13 * 2 ^ 3321929)%Z);[ | ].
*)
   match goal with
   |- ?a * INR ?e < IZR ?d =>
   let b := R_to_Z a in
   let b' := eval compute in (b * (Z.of_nat e))%Z in
   let c := decompose_big_number b' in
     assert (ltIZR: a * INR e = IZR c);[
     repeat (rewrite mult_IZR || rewrite plus_IZR);
     repeat (match goal with |- context[(_ ^ ?x)%Z] =>
             let  v := eval compute in (Z.abs_nat x) in
               change x with (Z.of_nat v) end;
             rewrite <- ?pow_IZR; simpl IZR; simpl INR; ring)|
       rewrite ltIZR; apply IZR_lt; apply Z.lt_trans with (2 ^ 14)%Z;
       [reflexivity | unfold precision; apply Z.pow_lt_mono_r; unfold prec; lia]]
   end.
  clear -num14; apply Rmult_lt_reg_r with 14;[psatzl R | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[|psatzl R].
  let v := R_to_Z 531 in let v' := decompose_big_number v in
  assert (dec500bz : v = v') by (apply Z.eqb_eq; reflexivity);
  replace 531 with (IZR v');
   [ | rewrite !plus_IZR, !mult_IZR;
     replace 2%Z with (Z.of_nat 2) by (compute; ring);
        rewrite <- pow_IZR; simpl IZR; ring]; rewrite <- dec500bz.
  rewrite num14, <- mult_IZR, <- Rpower_pow;[|psatzl R].
  replace (INR 19) with (IZR 19) by reflexivity.
  replace 2 with (IZR 2) by reflexivity.
  rewrite <- !Zpow_Rpower;
   [ |reflexivity | discriminate | reflexivity | discriminate].
  apply IZR_lt, Z.lt_trans with (precision * 2 ^ 4)%Z.
   apply Z.mul_lt_mono_pos_l;[ apply Z.pow_pos_nonneg;[| discriminate]|];
    reflexivity.
  unfold precision; rewrite <- Z.pow_add_r;
   [ |vm_compute; discriminate | vm_compute; discriminate].
(* l(500)/l(2) > 8.9657
   8.96 = 896/100 = 224/25
   but 500 is slightly less than 512 = 2 ^ 9, so I try
   224 + 9 * n / 25 + 9, to get the best approximation,
      this leads to (n = 4, 260/ 29
   500 ^ 29 > 2 ^ 260
   then 3321946 / 260 = 12776.7
*)
  apply Z.lt_trans with (2 ^ (260 * 12777))%Z.
   apply Z.pow_lt_mono_r;[reflexivity | vm_compute; discriminate | ].
   reflexivity.
  apply Z.lt_trans with (531 ^ (29 * 12777))%Z.
   repeat (rewrite Z.pow_mul_r;
     [ | rewrite <- Z.leb_le; vm_compute; reflexivity |
      vm_compute; discriminate ]).
   apply Z.pow_lt_mono_l;[reflexivity | ].
    split;[vm_compute; discriminate | ].
    rewrite <- Z.ltb_lt; vm_compute; reflexivity.
  apply Z.pow_lt_mono_r;[vm_compute; reflexivity | | ].
   apply Z.pow_nonneg; vm_compute; discriminate.
  vm_compute; reflexivity.
 assert (t'' := integer_pi precision gt1000 p0 19 nineteen1 t'); clear t'.
 rewrite andb_true_iff, ! Z.ltb_lt; intros ctr.
 assert (t' : Rabs (hR precision n - PI) <
        423 * Rpower 2 (-14) * Rpower 2 (-prec'r));[|clear t''].
  replace 423 with (21 * INR (19 + 1) + 3) by (simpl; ring).
  rewrite Rmult_assoc.
  replace (Rpower 2 (-14) * Rpower 2 (-prec'r)) with (/IZR precision).
   exact t''.
  rewrite <- Rpower_plus, <- Ropp_plus_distr, Rpower_Ropp, num14.
  rewrite qb', <- plus_IZR, num2.
  rewrite <- Zpow_Rpower;[ | reflexivity | ].
   repeat apply f_equal; reflexivity.
  compute; discriminate.
(* fold or change did not manage to avoid heavy computation here *)
 assert (p20 : (0 < 10 ^ (10 ^ 6 + 4))%Z).
  apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
 assert (cmpp : (10 ^ (10 ^ 6 + 4) < 2 ^ prec)%Z)
   by exact pow10million_pow2.
 assert (t := change_precision _ _ n p20 cmpp).
(* again, fold n' does not work here *)
 assert (t'' :
   hR precision n - / IZR (10 ^ (10 ^ 6 + 4)) <
   hR (10 ^ (10 ^ 6 + 4)) n' <= hR precision n) by exact t; clear t.
(* This does not work either
replace (n * 10 ^ (10 ^ 3 + 4) / precision)%Z with
  n' in t;[ | unfold n', precision].
*)
 assert (k0 : (0 < 10 ^ (10 ^ 6))%Z).
  apply Z.pow_pos_nonneg;[reflexivity | vm_compute; discriminate].
 assert (d0 : (0 < 10 ^ 4)%Z) by
    (rewrite <- Z.ltb_lt; vm_compute; reflexivity).
 assert (pwr : (10 ^ (10 ^ 6 + 4) = 10 ^ 10 ^ 6 * 10 ^ 4)%Z).
  rewrite <- Z.pow_add_r;[reflexivity | | ]; compute; discriminate.
(* BUG? : strange behavior: I can't use replace here because it
   performs too much computation. but this does not happen if pwr does
   not exist. Here is the tactic that does not work:
 replace (10 ^ 10 ^ 6 * 10 ^ 4)%Z with (10 ^ (10 ^ 6 + 4))%Z. *)
 assert (pwr2 : hR (10 ^ 10 ^ 6 * 10 ^ 4) n' = hR (10 ^ (10 ^ 6 + 4)) n').
  (unfold hR; rewrite pwr; reflexivity).
 assert (n'cl : Rabs (hR (10 ^ 10 ^ 6 * (10 ^ 4)) n' - PI) <
            426 * /IZR (10 ^ (10 ^ 6) * 10 ^ 4)).
  rewrite pwr2, <- pwr.
  assert (exists v, v = hR (10 ^ (10 ^ 6 + 4)) n') as [v hv].
   eapply ex_intro; eapply refl_equal.
  assert (exists vp, vp = precision) as [vp hvp].
   eapply ex_intro; eapply refl_equal.
  rewrite <- hv.
 (* BUG: I can't do this
 replace (v - PI) with
  ((v - hR vp n) + (hR vp n - PI)) by (clear; ring).  *)
   rewrite (helpring (hR precision n)).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rlt_trans with (/IZR (10 ^ (10 ^ 6 + 4)) +
                    423 * Rpower 2 (-14) * Rpower 2 (-prec'r)).
   apply Rplus_lt_compat.
    assert (0 < / IZR (10 ^ (10 ^ 6 + 4))).
     apply Rinv_0_lt_compat, (IZR_lt 0).
     apply Z.pow_pos_nonneg;[reflexivity | vm_compute; discriminate].
    apply Rabs_def1.
  (* BUG? : I don't understand why psatzl R can't do this one *)
     apply Rle_lt_trans with 0;[ | psatzl R].
     rewrite hv; apply Rle_minus; destruct t'' as [_ it]; exact it.
    apply Rplus_lt_reg_r with (hR precision n).
    unfold Rminus; rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, hv, Rplus_comm.
    destruct t'' as [it _]; exact it.
   exact t'.
  assert (num423 : 423 = IZR 423).
   change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
   reflexivity.
  assert (num426 : 426 = IZR 426).
   change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
   reflexivity.
  assert (num517 : 517 = IZR 517).
   change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
   reflexivity.
  rewrite qb', num423, num426, num14, num2.
  assert (0 < IZR (10 ^ (10 ^ 6 + 4))).
   apply (IZR_lt 0); apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
  apply Rmult_lt_reg_r with (IZR (10 ^ (10 ^ 6 + 4)));[assumption | ].
(* Bug? here, I can't finish the rewriting wit Rmult_1_r *)
  rewrite Rmult_plus_distr_r, 3!Rmult_assoc, Rinv_l;
   [ | apply Rgt_not_eq; assumption].
(* I have to set the instantiation precisely! *)
  rewrite (Rmult_1_r (IZR 426)).
  rewrite (Rmult_comm (Rpower (IZR 2) (-IZR u))
           (IZR (10 ^ (10 ^ 6 + 4)))).
  rewrite (Rmult_comm (Rpower (IZR 2) (-IZR 14))).
  rewrite <- 2!Rmult_assoc.
  apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR 14)).
   apply exp_pos.
  rewrite Rmult_plus_distr_r, !Rmult_assoc, <- Rpower_plus, Rplus_opp_l.
  rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
  apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR u)).
   apply exp_pos.
  rewrite Rmult_plus_distr_r, !Rmult_assoc, <- !Rpower_plus, Rplus_opp_l.
  rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
  rewrite <- !plus_IZR, <- Zpow_Rpower;
   [ | reflexivity | vm_compute; discriminate ].
  rewrite Rmult_1_l, <- !mult_IZR.
  rewrite <- plus_IZR.
  apply IZR_lt.
  change (2 ^ (14 + u) + (423 * 10 ^ (10 ^ 6 + 4)) <
     426 * 2 ^ (14 + u))%Z.
  assert (uq' : (14 + u = prec)%Z) by (rewrite <- Z.eqb_eq; vm_compute; reflexivity).
  rewrite uq'; apply Z.lt_trans with (2 * 10 ^ (10 ^ 6 + 4) + 423 * 10 ^ (10 ^ 6 + 4))%Z.
   apply Z.add_lt_mono_r.
   exact million_digit_lb_bin.
  rewrite <- Z.mul_add_distr_r; apply Z.mul_lt_mono_nonneg.
     rewrite <- Z.leb_le; vm_compute; reflexivity.
    rewrite <- Z.ltb_lt; vm_compute; reflexivity.
   apply Z.lt_le_incl, Z.pow_pos_nonneg;[| rewrite <- Z.leb_le; vm_compute]; reflexivity.
  exact pow10million_pow2.
 assert (b10pos : 0  < IZR (10 ^ 10 ^ 6 * 10 ^ 4)).
  apply (IZR_lt 0); rewrite <- Z.pow_add_r;
  try (rewrite <- Z.leb_le; vm_compute; reflexivity).
  change (0 < 10 ^ (10 ^ 6 + 4))%Z.
  apply Z.pow_pos_nonneg;[| rewrite <- Z.leb_le; vm_compute]; reflexivity.
 assert (ctr' :
  (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (426 * / IZR (10 ^ 10 ^ 6 * 10 ^ 4)) + 1 <
       n' mod 10 ^ 4 <
       10 ^ 4 -
       (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (426 * / IZR (10 ^ 10 ^ 6 * 10 ^ 4)) + 1))%Z).
  assert (sm: (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (426 * /IZR (10 ^ 10 ^ 6 * 10 ^ 4))
               = 426)%Z).
   unfold Rh; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
   [ | apply Rgt_not_eq; assumption].
   assert (num426 : 426 = IZR 426).
    change 1 with (IZR 1); repeat (rewrite <- plus_IZR || rewrite <- mult_IZR);
     reflexivity.
   unfold RbZ; rewrite num426, floor_IZR; reflexivity.
  rewrite sm. assumption.
  destruct (rerounding_simple (10 ^ 10 ^ 6) (10 ^ 4) _ PI n' d0 k0 n'cl ctr')
    as [rrs1 rrs2].
 split.
 (* psatzl does not do this one *)
  apply Rlt_Rminus; assumption.
 revert rrs2; unfold hR, Rdiv; rewrite plus_IZR.
 rewrite Rmult_plus_distr_r; intros rrs2.
 rewrite Rlt_minus_l; apply Rlt_le_trans with (1 := rrs2).
 rewrite Rplus_comm; apply Rplus_le_compat_r.
 apply Req_le; clear.
 change (IZR 1) with 1; rewrite Rmult_1_l, Rpower_Ropp.
 replace 10 with (IZR 10) by (simpl; ring).
 replace 6 with (IZR 6) by (simpl; ring).
 rewrite <- Zpow_Rpower;[ | reflexivity | compute; discriminate].
 rewrite <- Zpow_Rpower;[ | reflexivity | compute; discriminate].
 reflexivity.
unfold million_digit_pi; fold prec.
revert main.
lazy zeta.
set (cpt := hpi (2 ^ prec) 20).
unfold Z.modulo, Z.div at 3 5.
destruct (Z.div_eucl (cpt * 10 ^ (10 ^ 6 + 4) / (2 ^ prec)) (10 ^ 4))
  as (q, r).
unfold fst, snd; lazy zeta; tauto.
Qed.

(* In coq-8.4pl3, a bug in the implementation of psatzl prevents this
  file from being imported at the beginning of the session. *)
Require Import BigZ.
Require rounding_big.

Open Scope bigZ.

Lemma hdiv_morph p x y: [rounding_big.hdiv p x y] = hdiv [p] [x] [y].
Proof.
unfold hdiv, rounding_big.hdiv.
rewrite BigZ.spec_div, BigZ.spec_mul; reflexivity.
Qed.

Lemma hmult_morph p x y: [rounding_big.hmult p x y] = hmult [p] [x] [y].
Proof.
unfold hmult, rounding_big.hmult.
rewrite BigZ.spec_div, BigZ.spec_mul; reflexivity.
Qed.

Lemma hsqrt_morph p x: [rounding_big.hsqrt p x] = hsqrt [p] [x].
Proof.
unfold hsqrt, rounding_big.hsqrt.
rewrite BigZ.spec_sqrt, BigZ.spec_mul; reflexivity.
Qed.

Lemma h2_morph p : [rounding_big.h2 p] = h2 [p].
Proof.
unfold h2, rounding_big.h2. rewrite BigZ.spec_mul; reflexivity.
Qed.

Lemma hpi_rec_morph :
 forall p n v1 v2 v3, [rounding_big.hpi_rec p n v1 v2 v3]%bigZ =
   hpi_rec [p] n [v1] [v2] [v3].
intros p n; induction n as [ | n IHn]; intros v1 v2 v3.
 simpl.
 rewrite hmult_morph, BigZ.spec_add, hsqrt_morph, h2_morph; reflexivity.
change ([let sy := rounding_big.hsqrt p v1 in
          let ny := rounding_big.hdiv p (p + v1) (2 * sy) in
          let nz := rounding_big.hdiv p (p + rounding_big.hmult p v1 v2)
                       (rounding_big.hmult p (p + v2) sy) in
          rounding_big.hpi_rec p n ny nz
             (rounding_big.hmult p v3 (rounding_big.hdiv p (p + ny) (p + nz)))] =
          let sy := hsqrt [p] [v1] in
          let ny := hdiv [p] (h1 [p] + [v1]) (2 * sy) in
          let nz := hdiv [p] (h1 [p] + hmult [p] [v1] [v2])
                       (hmult [p] (h1 [p] + [v2]) sy) in
          hpi_rec [p] n ny nz
             (hmult [p] [v3] (hdiv [p] (h1 [p] + ny) (h1 [p] + nz)))).
lazy zeta; rewrite IHn; clear IHn.
 rewrite !hdiv_morph, !BigZ.spec_add, !BigZ.spec_mul, !hmult_morph, !hsqrt_morph.
 rewrite hdiv_morph, !BigZ.spec_add, !hdiv_morph, !BigZ.spec_mul, !BigZ.spec_add,
  !hmult_morph, !BigZ.spec_add, hsqrt_morph; reflexivity.
Qed.

Lemma hy1_morph p: [rounding_big.hy1 p] = hy1 [p].
Proof.
unfold rounding_big.hy1, hy1, rounding_big.hs2, hs2.
rewrite hdiv_morph, BigZ.spec_add, BigZ.spec_mul, !hsqrt_morph, h2_morph.
reflexivity.
Qed.

Lemma hz1_morph p : [rounding_big.hz1 p] = hz1 [p].
Proof.
unfold rounding_big.hz1, hz1, rounding_big.hs2, hs2.
rewrite !hsqrt_morph, h2_morph; reflexivity.
Qed.

Lemma hpi_morph : forall p n, [rounding_big.hpi p n]%bigZ = hpi [p]%bigZ n.
intros p; case n as [ | n].
 simpl; rewrite BigZ.spec_add, hsqrt_morph, h2_morph; reflexivity.
simpl; rewrite hpi_rec_morph, hdiv_morph, !BigZ.spec_add, !hy1_morph, !hz1_morph.
reflexivity.
Qed.

Lemma big_compute_eq : forall (p : bigZ) (q :Z) (d1 : bigZ) (d2 : Z) n,
  [p] = q -> [d1] = d2 ->
  fst (let precision := p in let n := rounding_big.hpi p n in
        let n' := n * d1 / p in
        let (q, r) := BigZ.div_eucl n' (10 ^ 4) in ((427 <? r) && (r <? 9573), q)) =
  fst (let precision := q in let n := hpi q n in
        let n' := (n * d2 / q)%Z in
        let (q, r) := Z.div_eucl n' (10 ^ 4) in
         ((427 <? r)%Z && (r <? 9573)%Z, q)) /\
  [snd (let precision := p in let n := rounding_big.hpi p n in
        let n' := n * d1 / p in
        let (q, r) := BigZ.div_eucl n' (10 ^ 4) in ((427 <? r) && (r <? 9573), q))] =
  snd (let precision := q in let n := hpi q n in
        let n' := (n * d2 / q)%Z in
        let (q, r) := Z.div_eucl n' (10 ^ 4) in
         ((427 <? r)%Z && (r <? 9573)%Z, q)).
Proof.
intros p q d1 d2 n pq d12.
lazy zeta.
generalize (BigZ.spec_div_eucl (rounding_big.hpi p n * d1 / p) (10 ^ 4)).
rewrite BigZ.spec_div, BigZ.spec_mul, hpi_morph, d12, pq.
replace [10 ^ 4] with (10 ^ 4)%Z by reflexivity.
case (BigZ.div_eucl _ _); intros q' r'; intros divq; rewrite <- divq.
split.
 rewrite !BigZ.spec_ltb; simpl; reflexivity.
simpl; reflexivity.
Qed.

Lemma big_million_eq : fst rounding_big.million_digit_pi = fst million_digit_pi /\
  [snd rounding_big.million_digit_pi] = snd million_digit_pi.
Proof.
unfold rounding_big.million_digit_pi, million_digit_pi.
apply big_compute_eq.
 rewrite BigZ.spec_pow.
 apply f_equal; reflexivity.
rewrite BigZ.spec_pow.
apply f_equal; reflexivity.
Qed.

Lemma big_pi_osix :
  fst rounding_big.million_digit_pi = true ->
    (IZR [snd rounding_big.million_digit_pi] * Rpower 10 (-(Rpower 10 6)) < PI <
    IZR [snd rounding_big.million_digit_pi] * Rpower 10 (-(Rpower 10 6))
   + Rpower 10 (-(Rpower 10 6)))%R.
destruct big_million_eq as [f s].
rewrite f, s.
(* replace here does not work: it triggers the humongous computation. *)
 assert (big : Rpower 10 (- Rpower 10 6) = /IZR (10 ^ 10 ^ 6)).
(* Here we need the clear tactic, otherwise, it again triggers a humongous
  computation.  I don't know why. *)
clear; rewrite Rpower_Ropp, !Zpow_Rpower; try (reflexivity || discriminate).
 replace (IZR 10) with 10%R by (simpl; ring).
 replace (IZR 6) with 6%R by (simpl; ring).
 reflexivity.
generalize pi_osix; unfold hR; rewrite big; intros tmp; exact tmp.
Qed.
