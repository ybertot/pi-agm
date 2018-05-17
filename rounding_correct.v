Require Import Psatz Reals Coquelicot.Coquelicot Interval.Interval_tactic
  generalities elliptic_integral agmpi.

Require Import Zwf.

Coercion INR : nat >-> R.
Open Scope R_scope.

Ltac approx_sqrt :=
 apply Rsqr_incrst_0; rewrite ?Rsqr_sqrt; unfold Rsqr; try apply sqrt_pos;
  psatzl R.

Lemma y_s n x (intx : 0 < x < 1) : y_ (S n) x = yfun (y_ n x).
Proof. now replace (S n) with (n + 1)%nat by ring; rewrite y_step. Qed.

Lemma z_s n x (n1 : (1 <= n)%nat) (intx : 0 < x < 1) : z_ (S n) x =
    (1 + z_ n x * y_ n x) / ((1 + z_ n x) * sqrt (y_ n x)).
Proof. now replace (S n) with (n + 1)%nat by ring; rewrite z_step. Qed.

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
    unfold y_, z_, a_, b_; simpl.
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
intros p p1; split; assert (t := ints).
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
  is_derive (fun y => (1 + z * y)/((1 + z) * sqrt y)) y
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
  e' < /10 -> e <= e' / 2 -> 1 <= y <= 71/50 -> Rabs h < e' ->
  let y1 := (1 + y)/(2 * sqrt y) in
  y1 - e' < r_div (1 + (y + h)) (2 * (r_sqrt (y + h))) < y1 + e'.
Proof using ce r_div_spec r_sqrt_spec.
intros ce' cc cy ch y1.
apply Rabs_def2 in ch.
assert (-/10 <= h <= /10) by psatzl R.
assert (0 <= e' <= /10) by psatzl R; assert (0 < e') by psatzl R.
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help3 : forall a b, a < b -> 0 < b -> a / b <= 1).
   intros a b ab b0; apply Rmult_le_reg_r with b;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c, a = (b - c) / e' -> b = c + a * e').
  now intros a b c q; rewrite q; field; psatzl R.
assert (exists e1, r_sqrt (y + h) = sqrt (y + h) + e1 *  e' /\
           -/2 <= e1 <= 0) as [e1 [Q Pe1]];[|rewrite Q; clear Q].
  destruct (r_sqrt_spec (y + h)) as [sc1 sc2]; try psatzl R.
  eapply ex_intro;split;[apply help4;reflexivity | ].
  now split;[ apply help1 | apply help2]; psatzl R.
assert (exists e2, r_div (1 + (y + h)) (2 * (sqrt (y + h) + e1 * e')) =
                   (1 + (y + h)) / (2 * (sqrt (y + h) + e1 * e')) + e2 * e' /\
                   -/2 <= e2 <= 0) as [e2 [Q Pe2]];[|rewrite Q; clear Q].
  destruct (r_div_spec (1 + (y + h)) (2 * (sqrt (y + h) + e1 * e')));
     [interval |].
  eapply ex_intro;split;[apply help4;reflexivity |].
  now split;[apply help1 | apply help2]; lt0.
set (y2 := (1 + (y + h)) / (2 * sqrt (y + h))).
assert (propagated_error : Rabs (y2 - y1) < e' / 14).
  destruct (MVT_abs yfun (fun x => (x - 1) / (4 * sqrt x ^ 3))
            y (y + h)) as [c [hc intc]].
    intros c intc; rewrite <- is_derive_Reals.
    apply derive_y_step; try psatzl R.
    now revert intc; destruct (Rle_dec 0 h);
        [rewrite Rmax_right, Rmin_left | rewrite Rmax_left, Rmin_right];
        psatzl R.
  assert (9/10 <= c <= 38/25).
    now revert intc; destruct (Rle_dec 0 h);
         [rewrite -> Rmin_left, Rmax_right | rewrite -> Rmin_right, Rmax_left];
         psatzl R.
  unfold y2, y1, yfun in hc |- *; rewrite hc, filter_Rlt.Rplus_minus_cancel1.
  now unfold Rdiv at 2; rewrite <- (Rmult_comm (/14));
    apply Rmult_le_0_lt_compat;try apply Rabs_pos;
       [interval with (i_bisect c)| apply Rabs_def1; tauto ].
split.
  replace (y1 - e') with (-(e' / 14) + (y1 + (0 - 13/14 * e'))) by field.
  apply Rabs_def2 in propagated_error.
  assert (help : forall a b c d e, a < e - b -> c < b + (d - e) -> a + c < d).
    now intros; psatzl R.
  apply help with (1 := proj2 propagated_error), Rplus_lt_compat_l; clear help.
  assert (help : forall a b c, a + b - c = a - c + b) by (intros; ring).
  rewrite help; clear help.
  apply Rplus_le_lt_compat.
    rewrite <- Rminus_le_0; unfold y2; apply Rmult_le_compat_l;[interval | ].
    apply Rle_Rinv;[interval | interval | apply Rmult_le_compat_l; [lt0 | ]].
    now assert (e1 * e' <= 0) by interval; lt0.
  now rewrite Ropp_mult_distr_l; apply Rmult_lt_compat_r; psatzl R.
replace (y1 + e') with ((e' / 14) + (y1 + (0  + 13/14 * e'))) by field.
apply Rabs_def2 in propagated_error.
assert (help : forall a b c d e, e - b < a -> b + (d - e) < c -> d < a + c).
  now intros; psatzl R.
apply help with (1 := proj1 propagated_error), Rplus_lt_compat_l; clear help.
assert (help : forall a b c, a + b - c = b + (a - c)) by (intros; ring).
rewrite help; clear help.
apply Rplus_le_lt_compat;[interval | ].
set (e'' := e1 * e' / sqrt (y + h)).
replace (2 * (sqrt (y + h) + e1 * e')) with
  (2 * (sqrt (y + h)) * (1 + e'')) by (unfold e''; field; interval).
unfold Rdiv; rewrite -> Rinv_mult_distr;
  [ | interval | unfold e''; interval].
(* test different values of the lower bound here.  Need at least /6 if propagated
   error is at /14, and then bisection on y is needed for interval *)
assert (- / 6 <= e'' <= 0) by (unfold e''; interval).
apply Rle_lt_trans with (y2 * (1 - e'' + 2 * e'' ^ 2) - y2).
  apply Rplus_le_compat_r; rewrite <- Rmult_assoc.
  apply Rmult_le_compat_l; unfold y2;[interval|].
  apply Rmult_le_reg_r with (1 + e'');[|rewrite Rinv_l];try lt0.
  replace ((1 - e'' + 2 * e'' ^ 2) * (1 + e'')) with
         ( 1 + e'' ^ 2 * ( 1 + 2 * e'')) by ring.
  now interval.
replace (y2 * (1 - e'' + 2 * e'' ^ 2) - y2) with
   (y2 * (- 1 + 2 * e'') *  (e1 / sqrt (y + h)) * e'); cycle 1.
  unfold e''; field; interval.
unfold y2.
(* just to look at what interval can do without directives.
interval_intro ((1 + (y + h)) / (2 * sqrt (y + h)) *
                  (-1 + 2 * e'') * (e1 / sqrt (y + h)) * e').
*)
apply Rmult_lt_compat_r;[lt0 | ].
unfold y2; interval with (i_bisect y).
Qed.

(* bounds on y and z are chosen to fit the actual values of y_1(1/sqrt 2)
  and z_1(1/sqrt 2). *)
Lemma z_error e' y z h h' :
  (e' < /50) -> (e <= e' / 4) -> 1 < y < 51/50 -> 1 < z < 6/5 ->
  Rabs h < e' -> Rabs h' < e' ->
  let v := (1 + z * y)/((1 + z) * sqrt y) in
  v - e' < r_div (1 + r_mult (z + h') (y + h))
                  (r_mult (1 + (z + h')) (r_sqrt (y + h))) < v + e'.
Proof using ce r_div_spec r_mult_spec r_sqrt_spec.
intros smalle' smalle inty intz he' h'e' v.
set (u := (1 + (z + h') * (y + h)) / ((1 + (z + h')) * sqrt (y + h))).
set (u' := (1 + z * (y + h)) / ((1 + z) * sqrt (y + h))).
apply Rabs_def2 in he'; apply Rabs_def2 in h'e'.
(* these are necessary for interval in its current version (3.1.1) *)
assert (1 <= y <= 51/50 /\ 1 <= z <= 6/5) as [iny' inz'] by psatzl R.
assert (-/50 <= h <= /50 /\ -/50 <= h' <= /50) as [inh inh'] by psatzl R.
assert (0 <= e' <= /50) by psatzl R.
assert (propagated_error : Rabs (u - v) < e'/ 5).
  replace (u - v) with (u - u' + (u' - v)) by ring.
  replace (e'/5) with (/10 * e' + /10 * e') by field.
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    destruct (MVT_abs (fun z => (1 + z * (y + h))/((1 + z) * sqrt (y + h)))
            (fun z => ((y + h) - 1) / ((z + 1) ^ 2 * sqrt (y + h)))
            z (z + h')) as [c [hc intc]].
      intros c intc; rewrite <- is_derive_Reals.
      apply derive_z_step; try psatzl R.
      now revert intc; destruct (Rle_dec 0 h');
        [rewrite Rmax_right, Rmin_left | rewrite Rmax_left, Rmin_right];
        psatzl R.
    assert (19/20 < c).
      now revert intc; destruct (Rle_dec 0 h');
         [rewrite Rmin_left | rewrite Rmin_right]; psatzl R.
    assert (19/20 <= c <= 13 /10).
      now split;[| apply Rle_trans with (1 := proj2 intc), Rmax_lub]; psatzl R.
    unfold u, u'; rewrite hc, filter_Rlt.Rplus_minus_cancel1.
    now apply Rmult_le_0_lt_compat;try apply Rabs_pos;
       [interval | apply Rabs_def1; tauto ].
  destruct (MVT_abs (fun y => (1 + z * y)/((1 + z) * sqrt y))
                (fun y => ((z * y - 1)/(2 * (1+z) * y * sqrt y)))
            y (y + h)) as [c [hc intc]].
    intros c intc; rewrite <- is_derive_Reals.
    apply z_step_derive_y; try psatzl R.
    now revert intc; destruct (Rle_dec 0 h);
        [rewrite Rmax_right, Rmin_left | rewrite Rmax_left, Rmin_right];
        psatzl R.
  assert (19/20 < c).
    now revert intc; destruct (Rle_dec 0 h);
         [rewrite Rmin_left | rewrite Rmin_right]; psatzl R.
  assert (19/20 <= c <= 11 /10).
    now split;[| apply Rle_trans with (1 := proj2 intc), Rmax_lub]; psatzl R.
  unfold u', v; rewrite hc, filter_Rlt.Rplus_minus_cancel1.
  now apply Rmult_le_0_lt_compat; try apply Rabs_pos;
       [interval | apply Rabs_def1; tauto ].
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help3 : forall a b, a < b -> 0 < b -> a / b <= 1).
   intros a b ab b0; apply Rmult_le_reg_r with b;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c, a = (b - c) / e' -> b = c + a * e').
  now intros a b c q; rewrite q; field; psatzl R.
assert (exists e1, r_mult (z + h') (y + h) = (z + h') * (y + h) + e1 * e' /\
                   - 1 / 4 <= e1 <= 0) as [e1 [Q Pe1]];[ | rewrite Q; clear Q].
  destruct (r_mult_spec  (z + h') (y + h)); try psatzl R.
  eapply ex_intro;split;[eapply help4, refl_equal | ].
  now split; [apply help1 | apply help2]; psatzl R.
assert (exists e2, r_sqrt (y + h) = sqrt (y + h) + e2 * e' /\
                - 1 / 4 <= e2 <= 0) as [e2 [Q Pe2]];[|rewrite Q; clear Q].
  destruct (r_sqrt_spec  (y + h)); try psatzl R.
  eapply ex_intro; split;[eapply help4, refl_equal | ].
  now split; [apply help1 | apply help2]; psatzl R.
assert (exists e3, r_mult (1 + (z + h')) (sqrt (y + h) + e2 * e') =
          (1 + (z + h')) * (sqrt (y + h) + e2 * e') + e3 * e' /\
          - 1 / 4 <= e3 <= 0) as [e3 [Q Pe3]];[|rewrite Q; clear Q].
  destruct (r_mult_spec (1 + (z + h')) (sqrt (y + h) + e2 * e')); try psatzl R.
    now interval.
  eapply ex_intro; split;[eapply help4, refl_equal | ].
  now split; [apply help1 | apply help2]; psatzl R.
assert (exists e4, r_div  (1 + ((z + h') * (y + h) + e1 * e'))
    ((1 + (z + h')) * (sqrt (y + h) + e2 * e') + e3 * e') =
     (1 + ((z + h') * (y + h) + e1 * e')) /
    ((1 + (z + h')) * (sqrt (y + h) + e2 * e') + e3 * e') + e4 * e'/\
    -1/4 <= e4 <= 0) as [e4 [Q Pe4]];[|rewrite Q; clear Q].
  destruct (r_div_spec  (1 + ((z + h') * (y + h) + e1 * e'))
    ((1 + (z + h')) * (sqrt (y + h) + e2 * e') + e3 * e') ); try psatzl R.
    now interval.
  eapply ex_intro;split;[eapply help4, refl_equal | ].
  now split;[apply help1|apply help2];psatzl R.
split.
  apply Rlt_le_trans with (u - e'/4 + -/4 * e'); cycle 1.
    apply Rplus_le_compat;[ | apply Rmult_le_compat_r; psatzl R].
    apply Rle_trans with ((1 + ((z + h') * (y + h) + e1 * e')) /
                          ((1 + (z + h')) * (sqrt (y + h)))); cycle 1.
      apply Rmult_le_compat_l;[interval | apply Rle_Rinv; try interval].
      apply Rle_trans with ((1 + (z + h')) * (sqrt (y + h) + e2 * e')).
        now assert (e3 * e' <= 0) by interval; psatzl R.
      apply Rmult_le_compat_l;[interval | ].
      now assert (e2 * e' <= 0) by interval; psatzl R.
    rewrite <- (Rplus_assoc _ _ (e1 * e')), (Rdiv_plus_distr _ (e1 * e')).
    apply Rplus_le_compat_l.
    unfold Rdiv; rewrite Ropp_mult_distr_r, (Rmult_comm _ e'), Rmult_assoc.
    now apply Rmult_le_compat_l;[psatzl R | interval].
  replace e' with (e' / 2 + (e' / 4 + /4 * e')) at 1 by field.
  unfold Rminus; rewrite !Ropp_plus_distr, <- 2!Rplus_assoc.
  apply Rplus_lt_le_compat;[apply Rplus_lt_compat_r | psatzl R].
  now apply Rabs_def2 in propagated_error; psatzl R.
rewrite <- (Rplus_assoc _ _ (e1 * e')), Rdiv_plus_distr.
assert (step : forall a b, b <= 0 -> a + b <= a) by (intros; psatzl R).
repeat (match goal with |- ?a + _ < _ => apply Rle_lt_trans with a end;
            [now apply step; interval | ]).
apply Rlt_trans with (u + 4 / 5 * e');cycle 1.
  now apply Rabs_def2 in propagated_error; psatzl R.
assert (help5 : forall a b c, a - b < c -> a < b + c) by (intros; psatzl R).
apply help5; match goal with |- ?a - _ < _ =>
  let c := constr: ((1 + (z + h') * (y + h)) /
              ((1 + (z + h')) * (sqrt (y + h) + e2 * e'))) in
  replace (a - u) with (a - c + (c - u)) by ring
  end.
apply Rlt_le_trans with (1 * ((13 / 50) * e') + 2 * ((13 / 50) * e'));
  [| psatzl R].
apply Rplus_lt_compat.
  assert (dd1 : forall a b c, -b < c -> is_derive (fun x => a /(b + x)) c
                                  ((fun x =>  -a / (b + x) ^ 2) c)).
    now intros a b c bc; auto_derive;[psatzl R | field; psatzl R].
  destruct (MVT_abs (fun c => (1 + (z + h') * (y  + h)) /
                        ((1 + (z + h')) * (sqrt (y + h) + e2 * e') + c))
                (fun c => -(1 + (z + h') * (y + h)) /
                            ((1 + (z + h')) * (sqrt (y + h) + e2 * e') + c)^2)
            0 (e3 * e')) as [c [hc intc]].
    intros c intc; rewrite <- is_derive_Reals; apply dd1.
    rewrite Rmin_right, Rmax_left in intc;[ | interval | interval].
    assert (- / 4 * e' <= e3 * e') by (apply Rmult_le_compat_r; try psatzl R).
    now assert (-/50 <= c <= 0) by psatzl R; interval.
  apply Rle_lt_trans with (1 := Rle_abs _).
  replace ((1 + (z + h')) * (sqrt (y + h) + e2 * e')) with
        ((1 + (z + h')) * (sqrt (y + h) + e2 * e') + 0) at 2 by ring.
  rewrite Rmin_right, Rmax_left in intc;[ | interval | interval].
  assert (-/4 * e' <= e3 * e') by (apply Rmult_le_compat_r; try psatzl R).
  assert (-/50 <= c <= 0) by psatzl R.
  rewrite hc; apply Rmult_le_0_lt_compat; try apply Rabs_pos;[interval | ].
  rewrite Rminus_0_r, Rabs_left1, Ropp_mult_distr_l;[ | interval].
  now apply Rmult_lt_compat_r; psatzl R.
replace u with
  ((1 + (z + h') * (y + h)) / ((1 + (z + h')) * (sqrt (y + h) + 0))) by
  (now unfold u; rewrite (Rplus_0_r)).
apply Rle_lt_trans with (1 := Rle_abs _).
assert (dd2 : (forall a b c d, 0 < b -> 0 < c -> -c < d ->
    is_derive (fun x => a / (b * (c + x))) d
              ((fun d => - a * b / (b * (c + d)) ^ 2) d))).
  intros a b c d b0 c0 cd; auto_derive;[ | field; psatzl R].
  now apply Rgt_not_eq, Rmult_lt_0_compat; psatzl R.
destruct (MVT_abs (fun c => (1 + (z + h') * (y + h)) /
                             ((1 + (z + h')) * (sqrt (y + h) + c)))
              (fun c => - (1 + (z + h') * (y + h)) * (1 + (z + h')) /
                           ((1 + (z + h')) * (sqrt (y + h) + c)) ^ 2) 0 (e2 * e'))
     as [c [hc intc]].
  intros c intc; rewrite <- is_derive_Reals; apply dd2;[interval | interval | ].
  rewrite Rmin_right, Rmax_left in intc;[ | interval | interval].
  assert (-/4 * e' <= e2 * e') by (apply Rmult_le_compat_r; try psatzl R).
  now assert (-/50 <= c <= 0) by psatzl R; interval.
rewrite Rmin_right, Rmax_left in intc;[ | interval | interval].
assert (-/4 * e' <= e2 * e') by (apply Rmult_le_compat_r; try psatzl R).
assert (-/50 <= c <= 0) by psatzl R.
rewrite hc; apply Rmult_le_0_lt_compat; try apply Rabs_pos;[interval | ].
rewrite Rminus_0_r, Rabs_left1, Ropp_mult_distr_l;[ | interval].
now apply Rmult_lt_compat_r; psatzl R.
Qed.

Lemma quotient_error : forall e' y z h h', e' < /40 ->
  Rabs h < e' / 2 -> Rabs h' < e' -> e <= e' / 4 ->
  1 < y < 51 / 50 -> 1 < z < 6 / 5 ->
  Rabs (r_div (1 + (y + h)) (1 + (z + h')) - (1 + y)/(1 + z)) <  13 / 10 * e'.
Proof using e ce r_div_spec.
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
    e < e2 / 5 -> /2 < p < 921/1000 ->
    /2 < v <= 1 -> Rabs h < e1 -> Rabs h' < e2 ->
    Rabs (r_mult (p + h) (v + h') - p * v) < e1 + 23/20 * e2.
Proof using ce r_mult_spec.
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

Fixpoint rpi_rec n s y z prod : R :=
  match n with
    0 => r_mult (2 + s) prod
  | S p =>
    let sy := r_sqrt y in
    let ny := (r_div (1 + y) (2 * (r_sqrt y))) in
    let nz := (r_div (1 + r_mult z y) (r_mult (1 + z) sy)) in
    rpi_rec p  s ny nz (r_mult prod (r_div (1 + ny) (1 + nz)))
  end.

Definition rs2 := r_sqrt 2.

Definition rsyz :=
  let s2 := rs2 in
  let ss2 := r_sqrt s2 in
  (s2, r_div (1 + s2) (2 * ss2), ss2).

Definition rpi1 :=
  let '(_, y1, z1) := rsyz in
  r_div (1 + y1) (1 + z1).

Definition rpi (n : nat) :=
  match n with
   O => 2 + r_sqrt 2
  | S p =>
    let '(s2, y1, z1) := rsyz in
    rpi_rec p s2 y1 z1 rpi1
  end.

Lemma ry_step : forall p y,
   (1 <= p)%nat ->
   Rabs (y - y_ p (/sqrt 2)) < 2 * e ->
   Rabs (r_div (1 + y) (2 * (r_sqrt y)) - y_ (p + 1) (/sqrt 2)) < 2 * e.
Proof using ce r_div_spec r_sqrt_spec.
intros p y p1 ch.
assert (double_e : 2 * e < / 10) by psatzl R.
set (h := y - y_ p (/sqrt 2)).
assert (double_eK : e <= (2 * e) / 2) by psatzl R.
set (y' := r_div (1 + y) (2 * (r_sqrt y))).
assert (inty' : 1 <= y_ p (/sqrt 2) <= 71/50).
 split; [apply Rlt_le, y_gt_1, ints |  ].
 destruct (eq_nat_dec p 1) as [pq1 | pn1].
  rewrite pq1; apply Rlt_le, Rlt_trans with (1 := y_1_ub); psatzl R.
 apply Rlt_le, Rlt_le_trans with (y_ 1 (/sqrt 2));
  [apply y_decr_n; try apply ints; try lia; try psatzl R | ].
 apply Rlt_le, Rlt_trans with (1 := y_1_ub);psatzl R.
generalize (y_error (2 * e) (y_ p (/sqrt 2)) h double_e double_eK
           inty' ch); lazy zeta.
fold (yfun (y_ p (/sqrt 2))); rewrite <- y_step;[ | exact ints].
replace (y_ p (/sqrt 2) + h) with y by (unfold h; ring); fold y'.
intros; apply Rabs_def1; psatzl R.
Qed.

Lemma rz_step :
  forall y z p, (1 <= p)%nat ->
  Rabs (y - y_ p (/sqrt 2)) < 2 * e ->
  Rabs (z - z_ p (/sqrt 2)) < 4 * e ->
  Rabs (r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y)) -
        z_ (p + 1) (/ sqrt 2)) < 4 * e.
Proof using r_div_spec r_mult_spec r_sqrt_spec ce.
intros y z p p1 cy cz.
set (h := y - y_ p (/sqrt 2)).
set (h' := z - z_ p (/sqrt 2)).
assert (cy' : Rabs h < 4 * e) by (unfold h; psatzl R).
assert (vs2 := ints).
assert (y1b := y_1_ub).
assert (inty : 1 < y_ p (/sqrt 2) < 51/50).
 split;[apply y_gt_1, ints |
  apply Rle_lt_trans with (y_ 1 (/sqrt 2)); try psatzl R].
 destruct (eq_nat_dec p 1) as [pq1 |];
  [rewrite pq1; psatzl R | apply Rlt_le, y_decr_n; auto; lia].
assert (be44 : e <= (4 * e) / 4) by psatzl R.
assert (four_e : 4 * e < /50) by psatzl R.
generalize (z_error (4 * e) (y_ p (/sqrt 2)) (z_ p (/sqrt 2)) h h'
             four_e be44 inty (int_z p p1) cy' cz).
lazy zeta. rewrite <- z_step; auto.
replace (y_ p (/ sqrt 2) + h) with y by (unfold h; ring).
replace (z_ p (/ sqrt 2) + h') with z by (unfold h'; ring).
intros; apply Rabs_def1; psatzl R.
Qed.

Lemma rprod_step :
  forall p y z prod, (1 <= p)%nat ->
    4 * (3/2) * p * e < /100 ->
    Rabs (y - y_ p (/sqrt 2)) < 2 * e ->
    Rabs (z - z_ p (/sqrt 2)) < 4 * e ->
    Rabs (prod - pr p) < 4 * (3/2) * p * e ->
   Rabs (r_mult prod (r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
              (1 + r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y))))
          - pr (p + 1)) < 4 * (3/2) * INR (p + 1) * e.
Proof using r_mult_spec r_div_spec r_sqrt_spec ce.
intros p y z prd p1 smallnp cy cz cprd.
assert (four_e : 4 * e < /40) by psatzl R.
assert (vs2 := ints).
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
              (1 + r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y))) -
               ((1 + y_ (p + 1) (/sqrt 2))/(1 + z_ (p + 1) (/sqrt 2))))
           < 13/10 * (4 * e)).
 set (h := r_div (1 + y) (2 * (r_sqrt y)) - y_ (p + 1) (/ sqrt 2)).
 set (h' := r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y)) - z_ (p + 1)
             (/ sqrt 2)).
 assert (cy' : Rabs h < (4 * e) / 2).
  apply Rlt_le_trans with (1 := ry_step p y p1 cy); psatzl R.
 assert (four_eK : e <= (4 * e) / 4) by psatzl R.
 generalize (quotient_error _ (y_ (p + 1) (/sqrt 2)) (z_ (p + 1) (/sqrt 2)) h h'
      four_e cy' (rz_step y z p p1 cy cz) four_eK inty' intz').
 replace (y_ (p + 1) (/sqrt 2) + h) with
      (r_div (1 + y) (2 * (r_sqrt y))) by (unfold h; ring).
 replace (z_ (p + 1) (/sqrt 2) + h') with
      (r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y)))
   by (unfold h'; ring).
 solve[auto].
assert (i2 : 0 <= 13/10 * (4 * e) <= /100) by psatzl R.
assert (e5K : e < (13/10 * (4 * e)) / 5) by psatzl R.
set (h := prd - pr p).
set (h' := r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
              (1 + r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y))) -
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
assert (inte : 0 <= 4 * (3/2) * p * e <= /100).
 split;repeat apply Rmult_le_pos; try apply pos_INR; psatzl R.
generalize (product_error_step (pr p) _
              _ (13/10 * (4 * e)) h h' inte i2 e5K pb qb cprd qbnd).
replace (pr p + h) with prd by (unfold h; ring).
replace ((1 + y_ (p + 1) (/sqrt 2)) / (1 + z_ (p + 1) (/ sqrt 2)) + h') with
          (r_div (1 + r_div (1 + y) (2 * (r_sqrt y)))
             (1 + r_div (1 + r_mult z y) (r_mult (1 + z) (r_sqrt y))))
   by (unfold h'; ring).
rewrite <- pr_step, <- (Rmult_comm (pr p)).
intros t; apply Rlt_le_trans with (1 := t).
 rewrite plus_INR, (Rmult_plus_distr_l _ p (INR 1)),
   (Rmult_plus_distr_r _ _ e); simpl (INR 1); psatzl R.
Qed.

Lemma rpi_rec_correct (p n : nat) s y z prod :
    (1 <= p)%nat -> 4 * (3/2) * (p + n) * e < /100 ->
    s = r_sqrt 2 ->
    Rabs (y - y_ p (/sqrt 2)) < 2 * e -> Rabs (z - z_ p (/sqrt 2)) < 4 * e ->
    Rabs (prod - pr p) < 4 * (3/2) * p * e ->
    Rabs (rpi_rec n s y z prod - agmpi (p + n)) <
      (2 + sqrt 2) * 4 * (3/2) * (p + n) * e + 2 * e.
Proof using r_sqrt_spec r_mult_spec r_div_spec ce.
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; interval).
assert (1189/1000 < sqrt (sqrt 2)) by interval.
intros p1 eb sq; rewrite sq; clear sq; revert p1 eb.
revert p y z prod; induction n.
 intros p y z prd p1; rewrite Nat.add_0_r; simpl (INR 0); rewrite Rplus_0_r.
intros smallp rny rnz rnpr.
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
 now repeat rewrite (Rmult_assoc (2 + sqrt 2)); apply Rmult_lt_compat_l; lt0.
intros p y z prd p1 pnsmall cy cz cprd.
assert (inty : 1 < y_ p (/sqrt 2) < 51/50).
 assert (t := ints).
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
 now assert (0 <= INR (S n)) by apply pos_INR; psatzl R.
assert (cvpn : (p + S n = S p + n)%nat) by ring.
assert (step_y := ry_step p y p1 cy).
assert (step_z := rz_step y z p p1 cy cz).
assert (step_prd := rprod_step p y z prd p1 ce' cy cz cprd).
assert (cvpn' : p + S n = ((1 + p)%nat) + n :> R).
  now rewrite !S_INR; simpl; ring.
rewrite S_INR; replace (p + (n + 1)) with ((1 + p)%nat + n) by
   (rewrite plus_INR; simpl; ring).
rewrite cvpn.
apply IHn; try (rewrite <- (Nat.add_comm p); assumption).
  lia.
rewrite <- cvpn'; assumption.
Qed.

Lemma ry1_correct : let '(_, y1 , _) := rsyz in
  Rabs (y1 - y_ 1 (/sqrt 2)) < 2 * e.
Proof using r_sqrt_spec r_div_spec ce.
assert (sqrt 2 - e <= r_sqrt 2 <= sqrt 2).
 assert (two_0 : 0 <= 2) by psatzl R.
 destruct (r_sqrt_spec 2 two_0); psatzl R.
assert (double_e_10 : 2 * e < /10) by psatzl R.
assert (double_eK : e <= (2 * e) / 2) by psatzl R.
assert (ints2 : 1 <= sqrt 2 <= 71/50) by interval.
assert (e0 : Rabs (r_sqrt 2 - sqrt 2) < 2 * e).
 apply Rabs_def1; psatzl R.
unfold rsyz.
generalize (y_error (2 * e) (sqrt 2) (r_sqrt 2 - sqrt 2) double_e_10
          double_eK ints2 e0); lazy zeta.
replace (sqrt 2 + (r_sqrt 2 - sqrt 2)) with (r_sqrt 2) by ring.
unfold rs2; set (ry1 := r_div (1 + r_sqrt 2) (2 * r_sqrt (r_sqrt 2))).
rewrite y_s, y_0; unfold yfun.
 intros; apply Rabs_def1; psatzl R.
split; interval.
Qed.

Lemma rz1_correct : let '(_, _, z1) := rsyz in
  Rabs (z1 - z_ 1 (/sqrt 2)) < 4 * e.
Proof using ce r_sqrt_spec.
unfold rsyz, rs2; rewrite z_1;[|split;interval].
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

Lemma ry1_bnd : let '(_, y1, _) := rsyz in
   1007/1000 < y1 < 52/50.
Proof using ce r_sqrt_spec r_div_spec.
unfold rsyz, rs2.
assert (help1 : forall a b c, 0 < a -> b * a < c -> b <= c / a).
   intros a b c a0 bac; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help2 : forall a b, 0 < a -> b <= 0 -> b / a <= 0).
   intros a b a0 ba; apply Rmult_le_reg_r with a;[psatzl R | ].
   now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
assert (help4 : forall a b c, a = (b - c) / e -> b = c + a * e).
  now intros a b c q; rewrite q; field; psatzl R.
assert (large_e : 0 <= e <= / 1000) by psatzl R.
assert (exists e1, r_sqrt 2 = sqrt 2 + e1 * e /\
                   - 1  <= e1 <= 0) as [e1 [Q Pe1]];[ | rewrite Q; clear Q].
  destruct (r_sqrt_spec 2); try psatzl R.
  eapply ex_intro;split;[eapply help4, refl_equal | ].
  now split; [apply help1 | apply help2]; psatzl R.
assert (exists e2, r_sqrt (sqrt 2 + e1 * e) =
             sqrt (sqrt 2 + e1 * e) + e2 * e /\
             -1 <= e2 <= 0) as [e2 [Q Pe2]];[ | rewrite Q; clear Q].
  destruct (r_sqrt_spec (sqrt 2 + e1 * e)); try interval.
  eapply ex_intro; split;[eapply help4, refl_equal | ].
  now split; [apply help1 | apply help2]; psatzl R.
assert (exists e3, r_div (1 + (sqrt 2 + e1 * e))
                     (2 * (sqrt (sqrt 2 + e1 * e) + e2 * e)) =
            (1 + (sqrt 2 + e1 * e)) /
             (2 * (sqrt (sqrt 2 + e1 * e) + e2 * e)) + e3 * e /\
             -1 <= e3 <= 0) as [e3 [Q Pe3]];[ | rewrite Q; clear Q].
  destruct (r_div_spec (1 + (sqrt 2 + e1 * e))
                     (2 * (sqrt (sqrt 2 + e1 * e) + e2 * e))); try interval.
  eapply ex_intro; split;[eapply help4, refl_equal | ].
  split; [apply help1 | apply help2]; psatzl R.
split; interval.
Qed.

Lemma rz1_bnd : let '(_, _, z1) := rsyz in
   1183/1000 < z1 < 119/100.
Proof using ce r_sqrt_spec.
unfold rsyz, rs2.
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; approx_sqrt).
assert (141/100 < r_sqrt 2 < 1415/1000).
 destruct (r_sqrt_spec 2); psatzl R.
assert (1187/1000 < sqrt (r_sqrt 2) < 119/100)
 by (split; approx_sqrt).
 destruct (r_sqrt_spec (r_sqrt 2)); psatzl R.
Qed.

Lemma q1_bnd : let '(_, y1, z1) := rsyz in
  90/100 < r_div (1 + y1) (1 + z1) < 94/100.
Proof using r_div_spec r_sqrt_spec ce.
assert (ty := ry1_bnd).
assert (tz := rz1_bnd).
revert ty tz; unfold rsyz, rs2; intros ty tz.
match goal with |- _ < r_div ?a ?b < _ =>
  destruct (r_div_spec a b) as [ld ud]; try psatzl R
end.
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
Proof using r_sqrt_spec r_div_spec ce.
assert (141/100 < sqrt 2 < 142/100) by (split; approx_sqrt).
assert (bnd_z1 : 1 < z_ 1 (/ sqrt 2) < 6/5).
  now rewrite z_1;[split | split]; interval.
replace (pr 1) with ((1 + y_ 1 (/sqrt 2)) / (1 + z_ 1 (/sqrt 2)))
 by (unfold pr; simpl; field; psatzl R).
assert (ty := ry1_correct).
assert (tz := rz1_correct).
unfold rpi1.
revert ty tz; destruct rsyz as [[rs2 ry1] rz1]; intros ty tz.
set (h := ry1 - y_ 1 (/sqrt 2)).
set (h' := rz1 - z_ 1 (/sqrt 2)).
assert (ty' : Rabs h < (4 * e) / 2)
  by (apply Rlt_le_trans with (1 := ty); psatzl R).
assert (four_e : 4 * e < /40) by psatzl R.
assert (four_eK : e <= (4 * e) / 4) by psatzl R.
assert (bnd_y1 : 1 < y_ 1 (/sqrt 2) < 51/50).
  now rewrite y_s, y_0; unfold yfun; split; interval.
generalize (quotient_error _ (y_ 1 (/sqrt 2)) (z_ 1 (/sqrt 2)) h h' four_e
         ty' tz four_eK bnd_y1 bnd_z1).
replace (1 + (y_ 1 (/ sqrt 2) + h)) with (1 + ry1) by (unfold h; ring).
replace (1 + (z_ 1 (/ sqrt 2) + h')) with (1 + rz1) by (unfold h'; ring).
intros; psatzl R.
Qed.

Lemma rpi_correct : forall n, (1 <= n)%nat -> 6 * n * e < /100 ->
  Rabs (rpi n - agmpi n) < (21 * n + 2) * e.
Proof using ce r_div_spec r_mult_spec r_sqrt_spec.
pattern 6 at 1; replace 6 with (4 * (3 / 2)) by field.
intros [|p] p1 cpe; [lia | ]; unfold rpi.
rewrite (Rmult_plus_distr_r _ _ e).
assert (rpi1_correct' : Rabs (rpi1 - pr 1) < 4 * (3 / 2) * INR 1 * e).
 simpl INR; rewrite Rmult_1_r; exact rpi1_correct.
rewrite -> S_INR, (Rplus_comm p) in cpe.
set (s2 := fst (fst rsyz)); set (ry1 := snd (fst rsyz));
set (rz1 := snd rsyz); unfold rsyz.
generalize (rpi_rec_correct 1 p s2 ry1 rz1 rpi1 (le_n _) cpe
           (eq_refl _) ry1_correct rz1_correct rpi1_correct').
intros t; apply Rlt_trans with (1 := t), Rplus_lt_compat_r.
rewrite -> (S_INR p), (Rplus_comm p); simpl (INR 1).
assert (0 <= p) by apply pos_INR.
repeat apply Rmult_lt_compat_r; try psatzl R;interval.
Qed.

Lemma precision_correct :
  forall n, (2 <= n)%nat -> (6 * n * e < / 100) ->
  Rabs (rpi n - PI) < agmpi n - PI + (21 * n + 2) * e.
Proof using ce r_div_spec r_mult_spec r_sqrt_spec.
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
  assert (PI < 10 /3) by interval.
  assert (7/5 < sqrt 2) by interval.
  psatzl R.
  assert (n1' : (1 <= n)%nat) by lia.
  destruct (bound_agmpi n n1'); replace (S n) with (n + 1)%nat by ring.
  assumption.
apply rpi_correct;[lia | assumption].
Qed.

Lemma million_correct :
  e = Rpower 10 (-(10 ^ 6 + 4)) ->
  Rabs (rpi 20 - PI) < /10 * Rpower 10 (-(10 ^ 6)).
Proof using ce r_div_spec r_mult_spec r_sqrt_spec.
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
     replace 4 with (INR 4) by (simpl; ring).
   rewrite Rpower_pow, Rpower_1; simpl; psatzl R.
  apply Rgt_not_eq, exp_pos.
 apply Rgt_not_eq, exp_pos.
assert (toe : (21 * 20 + 3) * e < /10 * Rpower 10 (- 10 ^ 6)).
 rewrite em, Ropp_plus_distr, Rpower_plus, (Rmult_comm (Rpower _ _)).
 rewrite <- Rmult_assoc; apply Rmult_lt_compat_r.
  solve[unfold Rpower; apply exp_pos].
 replace (-(4)) with (-INR 4) by (simpl; ring).
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

Variable magnifier : Z.
Close Scope R_scope.
Open Scope Z_scope.

Hypothesis big_magnifier : 1000 < magnifier.

Variable pos_magnifier : 0 < magnifier.

Lemma pos_magnifierR : (0 < IZR magnifier)%R.
Proof using pos_magnifier.
apply (IZR_lt 0); exact pos_magnifier.
Qed.

Definition hmult x y := x * y / magnifier.
Definition hsqrt x := Z.sqrt(magnifier * x).
Definition hdiv x y := (x * magnifier)/y.
Definition h1 := magnifier.
Definition h2 := 2 * h1.

(* These few lines to make the code robust to a bug present in
 coq-8.4pl2, but not in later versions of Coq. *)
Definition floor : R -> Z := Rcomplements.floor.

Lemma floorP (x : R) :  (IZR (floor x) <= x < IZR (floor x) + 1)%R.
Proof using.
unfold floor, Rcomplements.floor.
destruct floor_ex as [v vp]; simpl; psatzl R.
Qed.

Definition hR (v : Z) : R := (IZR v /IZR magnifier)%R.

Definition RbZ (v : R) : Z := floor v.

Definition Rh (v : R) : Z := RbZ( v * IZR magnifier).


Fixpoint hpi_rec (n : nat) (s2 y z prod : Z) : Z :=
  match n with
    0%nat => hmult (h2 + s2) prod
  | S p =>
    let sy := hsqrt y in let ny := hdiv (h1 + y) (2 * sy) in
    let nz := hdiv (h1 + hmult z y) (hmult (h1 + z) sy) in
    hpi_rec p s2 ny nz (hmult prod (hdiv (h1 + ny) (h1 + nz)))
  end.

Definition r_div (x y : R) := hR (Rh (x / y)).

Definition r_mult (x y : R) : R := hR (Rh (x * y)).

Definition r_sqrt (x : R) : R := hR (Rh (sqrt x)).

Lemma hdiv_spec :
  forall x y : Z, 0 < y -> hR (hdiv x y) = r_div (hR x) (hR y).
Proof using pos_magnifier.
intros x y y0; unfold hdiv, r_div, hR.
replace (IZR x/ IZR magnifier / (IZR y / IZR magnifier))%R with
 (IZR x / IZR y)%R by
   (field; split; apply Rgt_not_eq, (IZR_lt 0); assumption).
apply f_equal with (f := fun x => (IZR x / IZR magnifier)%R).
unfold Rh, RbZ.
replace (IZR x/IZR y * IZR magnifier)%R with
  (IZR x * IZR magnifier/IZR y)%R
 by (field; apply Rgt_not_eq, (IZR_lt 0); assumption).
rewrite <- mult_IZR.
assert (t := Z.div_unique_pos).
set (v := (IZR (x * magnifier) / IZR y)%R).
destruct (floorP v) as [qle qcl].
simpl; symmetry; apply Z.div_unique_pos with
  (x * magnifier - floor v * y)%Z; try ring.
assert (floor v * y <= x * magnifier)%Z.
 apply le_IZR; rewrite mult_IZR; apply Rmult_le_reg_r with (/IZR y)%R.
  apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
 rewrite Rmult_assoc, Rinv_r, Rmult_1_r;[exact qle | ].
 apply Rgt_not_eq, (IZR_lt 0); assumption.
split;[lia | ].
assert (x * magnifier < floor v * y + y)%Z;[ | lia].
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
Proof using pos_magnifier.
intros x y x0 y0; unfold hmult, r_mult, hR.
replace (IZR x / IZR magnifier * (IZR y /IZR magnifier))%R
 with (IZR x * IZR y /(IZR magnifier*IZR magnifier))%R;
[|field;apply Rgt_not_eq, (IZR_lt 0); assumption].
apply f_equal with (f := (fun x => IZR x /IZR magnifier)%R).
unfold Rh, RbZ.
match goal with |- context[floor ?a] => set (v := a) end.
destruct (floorP v) as [qle qcl].
symmetry.
apply Z.div_unique_pos with (x * y - floor v * magnifier); try lia.
assert (floor v * magnifier <= x * y).
 apply le_IZR; rewrite !mult_IZR.
 apply Rmult_le_reg_r with (/IZR magnifier)%R;
  [apply Rinv_0_lt_compat, (IZR_lt 0); assumption | ].
 rewrite Rmult_assoc, Rinv_r, Rmult_1_r;
  [|apply Rgt_not_eq, (IZR_lt 0); assumption].
apply Rle_trans with (1 := qle); apply Req_le; unfold v; field;
 apply Rgt_not_eq, (IZR_lt 0); assumption.
assert (x * y < floor v * magnifier + magnifier);[|lia].
 replace (floor v * magnifier + magnifier) with
  ((floor v + 1) * magnifier) by ring.
apply lt_IZR; rewrite !mult_IZR, plus_IZR.
simpl (IZR 1).
apply Rmult_lt_reg_r with (/IZR magnifier)%R;
  [apply Rinv_0_lt_compat, (IZR_lt 0); assumption | ].
rewrite (Rmult_assoc (_ + _)), Rinv_r, Rmult_1_r;
 [|apply Rgt_not_eq, (IZR_lt 0); assumption].
apply Rle_lt_trans with (2 := qcl), Req_le; unfold v; field;
apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma hsqrt_spec :
  forall x : Z, (0<= x -> hR (hsqrt x) = r_sqrt (hR x))%Z.
Proof using pos_magnifier.
intros x x0; unfold hsqrt, r_sqrt, hR.
assert (0 < IZR magnifier)%R by (apply (IZR_lt 0); assumption).
apply f_equal with (f := fun x => (IZR x / IZR magnifier)%R).
unfold Rh, RbZ;
match goal with |- context[floor ?a] => set (v := a) end.
destruct (floorP v) as [vle vcl].
apply Z.sqrt_unique; split.
 apply le_IZR; rewrite mult_IZR.
 apply sqrt_le_0;[apply Rle_0_sqr | | ].
  rewrite mult_IZR; apply Rmult_le_pos.
   apply Rlt_le; assumption.
  apply (IZR_le 0); assumption.
 rewrite sqrt_square.
  apply Rle_trans with (1 := vle), Req_le.
  unfold v; rewrite sqrt_div_alt;[ | assumption].
 unfold Rdiv; rewrite Rmult_assoc.
  pattern (IZR magnifier) at 2;
  replace (IZR magnifier) with (sqrt(IZR magnifier) * sqrt(IZR magnifier))%R.
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
unfold Rdiv; pattern (IZR magnifier) at 2;
replace (IZR magnifier) with (sqrt(IZR magnifier) * sqrt(IZR magnifier))%R.
 rewrite Rmult_assoc, <- (Rmult_assoc (/sqrt(IZR magnifier))),
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
Proof using pos_magnifier.
intros x y x0 y0; unfold hdiv.
apply Z.div_pos.
 apply Z.mul_nonneg_nonneg.
  assumption.
 apply Z.lt_le_incl; assumption.
assumption.
Qed.

Lemma hmult_pos :
  forall x y, 0 <= x -> 0 <= y -> 0 <= hmult x y.
Proof using pos_magnifier.
intros x y x0 y0; unfold hmult.
apply Z.div_pos.
 apply Z.mul_nonneg_nonneg; assumption.
assumption.
Qed.

Lemma hsqrt_pos :
  forall x, 0 <= hsqrt x.
Proof using.
intros x; unfold hsqrt; apply Z.sqrt_nonneg.
Qed.

Lemma hR_half_non_zero : forall x, (/2 < hR x)%R -> 0 < x.
Proof using pos_magnifier.
intros x cx; apply lt_IZR.
simpl (IZR 0).
unfold hR in cx; apply Rmult_lt_reg_r with (/IZR magnifier)%R.
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
apply Rlt_trans with (2 := cx); rewrite Rmult_0_l; psatzl R.
Qed.

Lemma hplus_spec : forall x y, (hR (x + y) = hR x + hR y)%R.
Proof using.
intros; unfold hR, Rdiv.
rewrite plus_IZR, Rmult_plus_distr_r; reflexivity.
Qed.

Lemma hscal2_spec : forall x, (hR (2 * x) = 2 * hR x)%R.
Proof using.
intros; unfold hR, Rdiv.
rewrite mult_IZR, Rmult_assoc; reflexivity.
Qed.

Lemma h1_spec : hR h1 = 1%R.
Proof using pos_magnifier.
unfold hR, Rdiv; apply Rinv_r; apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma h2_spec : hR h2 = 2%R.
Proof using pos_magnifier.
unfold hR, Rdiv, h2, h1; rewrite mult_IZR; simpl (IZR 2).
field; apply Rgt_not_eq, (IZR_lt 0); assumption.
Qed.

Lemma hR_gt_0 : forall x, (0 < hR x)%R -> 0 < x.
Proof using pos_magnifier.
intros x x0; apply (lt_IZR 0); simpl (IZR 0).
apply (Rmult_lt_reg_r (/IZR magnifier)).
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
rewrite Rmult_0_l; exact x0.
Qed.

Lemma floor_IZR (v : Z) : floor (IZR v) = v.
Proof using.
clear.
destruct (floorP (IZR v)) as [xle xcl].
apply le_IZR in xle.
revert xcl; replace 1%R with (IZR 1) by reflexivity; rewrite <- plus_IZR.
intros xcl; apply lt_IZR in xcl; lia.
Qed.

Lemma Rh_hR (v : Z) : Rh (hR v) = v.
Proof using pos_magnifier.
unfold Rh, RbZ, hR.
replace (IZR v / IZR magnifier * IZR magnifier)%R with (IZR v)%R.
 rewrite floor_IZR; reflexivity.
field; apply Rgt_not_eq, pos_magnifierR.
Qed.

Lemma hR_pos : forall x, (0 <= hR x)%R -> 0 <= x.
Proof using pos_magnifier.
intros x x0; apply (le_IZR 0); simpl (IZR 0).
apply (Rmult_le_reg_r (/IZR magnifier)).
 apply Rinv_0_lt_compat, (IZR_lt 0); assumption.
rewrite Rmult_0_l; exact x0.
Qed.

Lemma h2_pos : 0 < h2.
Proof using pos_magnifier.
unfold h2; apply Z.mul_pos_pos.
 reflexivity.
assumption.
Qed.

Lemma h1_pos : 0 < h1.
Proof using pos_magnifier.
assumption.
Qed.

Open Scope R_scope.

Lemma hR_Rh (v : R) : v - /IZR magnifier < hR (Rh v) <= v.
Proof using pos_magnifier.
unfold hR, Rh, RbZ.
destruct (floorP (v * IZR magnifier)) as [xle xcl].
assert (pm:= pos_magnifierR).
split.
 replace (v - / IZR magnifier) with
   ((v * IZR magnifier - 1)/IZR magnifier) by (field; psatzl R).
 apply Rmult_lt_compat_r;[apply Rinv_0_lt_compat | ]; try psatzl R.
apply Rmult_le_reg_r with (IZR magnifier);[assumption | ].
unfold Rdiv; rewrite Rmult_assoc, Rinv_l; psatzl R.
Qed.

Lemma r_div_spec : forall x y, 0 < y ->
   x / y - /IZR magnifier < r_div x y <= x / y.
Proof using pos_magnifier.
intros x y y0; unfold r_div; apply hR_Rh.
Qed.

Lemma r_mult_spec : forall x y, 0 <= x -> 0 <= y ->
   x * y - /IZR magnifier < r_mult x y <= x * y.
Proof using pos_magnifier.
intros x y x0 y0; unfold r_mult; apply hR_Rh.
Qed.

Lemma r_sqrt_spec : forall x, 0 <= x ->
    sqrt x - /IZR magnifier < r_sqrt x <= sqrt x.
Proof using pos_magnifier.
intros; apply hR_Rh.
Qed.

Lemma dummy : 0 < /IZR magnifier < /1000.
Proof using big_magnifier pos_magnifier.
split;[apply Rinv_0_lt_compat, (IZR_lt 0); assumption|].
apply Rinv_1_lt_contravar;[psatzl R | ].
replace 1%R with (IZR 1) by reflexivity;
repeat (rewrite <- plus_IZR || rewrite <- mult_IZR); simpl Zmult.
apply IZR_lt; assumption.
Qed.

Lemma hpi_rpi_rec (n p : nat) s2 y z prod:
    (1 <= p)%nat ->
    s2 = hsqrt h2 ->
    4 * (3/2) * INR (p + n) * /IZR magnifier < /100 ->
    Rabs (hR y - y_ p (/sqrt 2)) < 2 * /IZR magnifier ->
    Rabs (hR z - z_ p (/sqrt 2)) < 4 * /IZR magnifier ->
    Rabs (hR prod - pr p) < 4 * (3/2) * INR p * /IZR magnifier ->
    hR (hpi_rec n s2 y z prod) =
    rpi_rec r_div r_sqrt r_mult n (hR s2) (hR y) (hR z) (hR prod).
Proof using big_magnifier pos_magnifier.
intros p1 s2q; rewrite s2q; clear s2q s2.
revert p y z prod p1.
assert (/IZR magnifier < /100).
 apply Rinv_1_lt_contravar;[psatzl R |].
 replace 100 with (IZR 100) by (simpl; psatzl R).
 apply IZR_lt; apply Z.lt_trans with 1000%Z;[reflexivity |assumption].
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
(* TODO : remove condition on an arbitrary error in and prod_bnd *)
 apply Rabs_def2 in cprd; psatzl R.
assert (0 <= h2)%Z by (apply Z.lt_le_incl, h2_pos).
assert (/4 < hR y).
 apply Rabs_def2 in cy; assert (t:= y_gt_1 (/sqrt 2) p ints); psatzl R.
assert (/2 < sqrt (hR y)) by approx_sqrt.
destruct (r_sqrt_spec (hR y)); try psatzl R.
assert (0 <= y)%Z by (apply hR_pos; psatzl R).
assert (0 < hsqrt y)%Z.
 apply hR_gt_0; rewrite hsqrt_spec; try psatzl R; assumption.
assert (0 < 2 * hsqrt y)%Z.
 apply Z.mul_pos_pos; [reflexivity | assumption].
assert (0 <= hsqrt y)%Z by (apply Z.lt_le_incl; assumption).
set (ny := r_div (1 + hR y) (2 * (r_sqrt (hR y)))).
set (nz := r_div (1 + r_mult (hR z) (hR y))
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
             hR (hdiv (h1 + hmult z y) (hmult (h1 + z) (hsqrt y)))).
 unfold nz.
 now rewrite hdiv_spec, hplus_spec, !hmult_spec, hplus_spec, hsqrt_spec, h1_spec;
 auto.
change (hR (hpi_rec (S n) (hsqrt h2) y z prd) =
         rpi_rec r_div r_sqrt r_mult n (hR (hsqrt h2)) ny nz
         (r_mult (hR prd) (r_div (1 + ny) (1 + nz)))).
set (ny' := hdiv (h1 + y) (2 * hsqrt y)).
set (nz' := hdiv (h1 + hmult z y) (hmult (h1 + z) (hsqrt y))).
replace (hpi_rec (S n) (hsqrt h2) y z prd) with
       (hpi_rec n (hsqrt h2) ny' nz'
        (hmult prd (hdiv (h1 + ny') (h1 + nz')))) by reflexivity.
set (npr := r_mult (hR prd) (r_div (1 + ny) (1 + nz))).
assert (4 * (3/2) * INR p * / IZR magnifier < /100).
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
(* TODO : improve the magnifier. *)
assert (cy' : Rabs (hR y - y_ p (/sqrt 2)) < 2 * / IZR magnifier) by psatzl R.
assert (tz := rz_step _ r_div r_sqrt r_mult dummy r_mult_spec r_div_spec
         r_sqrt_spec (hR y) (hR z) p p1 cy' cz).
fold ny in ty; fold nz in tz.
assert (/4 * /2 <= hR y * hR z)%R.
 apply Rmult_le_compat; psatzl R.
assert (y_p1p : (1 < y_ (p + 1) (/sqrt 2))%R).
 apply y_gt_1, ints.
assert (z_p1p : (1 <= z_ (p + 1) (/sqrt 2))%R).
 apply Rlt_le, z_gt_1;[apply ints | lia ].
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
Proof using pos_magnifier big_magnifier.
unfold hs2; rewrite hsqrt_spec, h2_spec;[ |apply Z.lt_le_incl, h2_pos].
assert (1414/1000 < sqrt 2 < 1415/1000) by (split; approx_sqrt).
assert (/IZR magnifier < / 1000).
  apply Rinv_1_lt_contravar; [psatzl R | replace 1000 with (IZR (40 * 25))].
    apply IZR_lt; assumption.
  rewrite mult_IZR; simpl; ring.
destruct (r_sqrt_spec 2); psatzl R.
Qed.

Lemma hss2_bnd : 117/100 < hR (hsqrt hs2) < 119/100.
Proof using pos_magnifier big_magnifier.
assert (hs2b := hs2_bnd).
assert (1187/1000 < sqrt (hR hs2) < 119/100) by (split; approx_sqrt).
assert (/IZR magnifier < / 1000).
  apply Rinv_1_lt_contravar; [psatzl R | replace 1000 with (IZR (40 * 25))].
   apply IZR_lt; assumption.
  rewrite mult_IZR; simpl; ring.
rewrite hsqrt_spec;[ | apply hR_pos; psatzl R].
destruct (r_sqrt_spec (hR hs2)); psatzl R.
Qed.

Definition hsyz :=
  let s2 := hs2 in
  let ss2 := hsqrt hs2 in
  (hs2, hdiv (h1 + hs2) (2 * ss2), ss2).

Lemma hy1_spec : hR (snd (fst (hsyz))) = snd (fst (rsyz r_div r_sqrt)).
Proof using big_magnifier pos_magnifier.
unfold hsyz, hs2.
assert (t := h2_pos).
assert (t' := Z.lt_le_incl _ _ h2_pos).
destruct hs2_bnd.
assert (0 <= hsqrt h2)%Z.
 apply hR_pos; fold hs2; psatzl R.
destruct hss2_bnd.
assert (0 <= hsqrt hs2)%Z.
 now apply hR_pos; psatzl R.
unfold hsyz, hs2, fst, snd.
rewrite hdiv_spec, hplus_spec, hscal2_spec, !hsqrt_spec,
    h2_spec, h1_spec; auto.
apply Z.mul_pos_pos;[compute; reflexivity | ].
fold hs2; apply hR_gt_0; psatzl R.
Qed.

Lemma hz1_spec : hR (snd hsyz) = snd (rsyz r_div r_sqrt).
Proof using big_magnifier pos_magnifier.
assert (t := Z.lt_le_incl _ _ h2_pos).
unfold hsyz, fst, snd, hs2; rewrite !hsqrt_spec, h2_spec; auto.
apply hR_pos; fold hs2; destruct hs2_bnd; psatzl R.
Qed.

Definition hpi n :=
  match n with
    O => (h2 + hsqrt h2)%Z
  | S p => let '(s2, y1, z1) := hsyz in
       hpi_rec p s2 y1 z1 (hdiv (h1 + y1) (h1 + z1))
  end.

Lemma hpi_rpi (n : nat) :
  6 * INR n * /IZR magnifier < / 100 ->
  hR (hpi n) = rpi r_div r_sqrt r_mult n.
Proof using big_magnifier pos_magnifier.
destruct n as [ | n]; intros small_e.
 simpl; rewrite hplus_spec, hsqrt_spec, h2_spec.
  reflexivity.
 apply Z.lt_le_incl; exact h2_pos.
assert (1 <= 1)%nat by lia.
assert (4 * (3/2) * S n * / IZR magnifier</100).
 replace (4 * (3/2)) with 6 by field; assumption.
assert (0 < / IZR magnifier < / 1000) by exact dummy.
assert (Rabs (hR (snd (fst hsyz)) - y_ 1 (/sqrt 2)) < 2 * / IZR magnifier).
 rewrite hy1_spec; apply ry1_correct; auto.
  apply r_div_spec.
 apply r_sqrt_spec.
assert (0 < h1 + snd hsyz)%Z.
 apply Z.add_pos_pos;[apply h1_pos | ].
 change ((0 < snd hsyz)%Z); apply hR_gt_0; rewrite hz1_spec.
 unfold rsyz, snd.
(* This is a hack to make the script robust to a change of behavior between
   coq-8.5 and coq-8.6.  See also uses of rz1_correct three lines further
   below.  It should be removed in the long run. *)
 assert (t := rz1_bnd _ _ _ dummy r_div_spec r_sqrt_spec) ||
   assert (t := rz1_bnd _ r_div _ dummy r_sqrt_spec).
 unfold rsyz in t; psatzl R.
assert (Rabs (hR (snd hsyz) - z_ 1 (/sqrt 2)) < 4 * / IZR magnifier).
  rewrite hz1_spec;
    (apply (rz1_correct _ _ _ dummy r_div_spec r_sqrt_spec) ||
     apply (rz1_correct _ r_div _ dummy r_sqrt_spec)); auto.
assert (Rabs (hR (hdiv (h1 + snd (fst hsyz)) (h1 + snd hsyz)) - pr 1) <
         4 * (3 / 2) * 1%nat * / IZR magnifier).
 simpl INR; rewrite Rmult_1_r.
 rewrite hdiv_spec, !hplus_spec, hy1_spec, hz1_spec, h1_spec; auto.
 change (r_div (1 + snd (fst (rsyz r_div r_sqrt)) )
               (1 + snd (rsyz r_div r_sqrt)))
   with (rpi1 r_div r_sqrt).
 apply rpi1_correct;[apply dummy | apply r_div_spec | apply r_sqrt_spec].
generalize hy1_spec.
unfold hpi, hsyz, snd, fst, rsyz; intros hy1_spec'.
rewrite (hpi_rpi_rec n 1), hy1_spec', hdiv_spec; auto.
assert (0 < h2)%Z.
  now unfold h2, h1; lia.
assert (0 < hs2)%Z.
  now unfold hs2, hsqrt; rewrite Z.sqrt_pos; apply Z.mul_pos_pos; auto.
unfold rpi, rsyz.
rewrite !hplus_spec, h1_spec, hy1_spec', !hsqrt_spec; try lia.
unfold hs2, rs2; rewrite hsqrt_spec, h2_spec; try lia.
reflexivity.
Qed.

Lemma Zpow_Rpower : forall x y, (0 < x) %Z -> (0 <= y)%Z ->
   IZR (x ^ y) = Rpower (IZR x) (IZR y). (* standard *)
Proof using.
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
  forall n, hpi (n + 1) = hpi_rec n hs2 (snd (fst hsyz))
                (snd hsyz) (hdiv (h1 + snd (fst hsyz) )
                                 (h1 + snd hsyz)).
Proof using.
intros n; replace (n + 1)%nat with (S n) by ring; reflexivity.
Qed.

Lemma integer_pi :
  forall n, (1 <= n)%nat ->
  600 * INR (n + 1) < IZR magnifier < Rpower 531 (2 ^ n)/ 14 ->
  Rabs (hR (hpi (n + 1)) - PI)
     < (21 * INR (n + 1) + 3) /IZR magnifier.
Proof using big_magnifier pos_magnifier.
intros n n1; replace (600 * INR (n + 1)) with (6 * INR (n + 1) * 100) by ring.
intros intp.
assert (msp := r_mult_spec).
assert (dsp := r_div_spec).
assert (ssp := r_sqrt_spec).
assert (Rp0 : 0 < IZR magnifier).
 apply (IZR_lt 0); assumption.
assert (vp0 : 0 < /IZR magnifier).
 apply Rinv_0_lt_compat; assumption.
replace ((21 * INR (n + 1) + 3) / IZR magnifier) with
  (/IZR magnifier + (21 * INR (n + 1) + 2) /IZR magnifier);
 [|field; apply Rgt_not_eq; assumption].

apply Rlt_trans with
  (agmpi (n + 1) - PI + (21 * INR (n + 1) + 2) * / IZR magnifier).
 assert (/IZR magnifier < /1000).
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
(* This is a hack to make the script robust to a change of behavior between
   coq-8.5 and coq-8.6.  It should be removed in the long run. *)
( destruct (rz1_bnd (/IZR magnifier) r_div r_sqrt) as [lz1 uz1];
   [psatzl R | exact r_div_spec | exact r_sqrt_spec | ]) ||
  (destruct (rz1_bnd (/IZR magnifier) r_div r_sqrt) as [lz1 uz1];
   [psatzl R | exact r_sqrt_spec | ]).
 assert (hpi1_spec : hR (hdiv (h1 + snd (fst hsyz))
                        (h1 + snd hsyz)) = rpi1 r_div r_sqrt).
  unfold rpi1; rewrite hdiv_spec, !hplus_spec, h1_spec, hy1_spec, hz1_spec;
   auto.
  apply hR_gt_0; rewrite hplus_spec, h1_spec, hz1_spec.
  unfold rsyz; simpl; psatzl R.
 assert (0 < 6 * INR (n + 1)).
  apply Rmult_lt_0_compat;[psatzl R | apply lt_0_INR; lia].
 assert (bp : 6 * INR (n + 1) * / IZR magnifier < /100).
  apply (Rmult_lt_reg_l (/ (6 * INR (n + 1)))).
   apply Rinv_0_lt_compat; assumption.
   rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;
       [ | apply Rgt_not_eq; assumption].
  rewrite <- Rinv_mult_distr;[|psatzl R|psatzl R].
  apply Rinv_1_lt_contravar.
   assert (1 < INR ( n + 1));[apply lt_1_INR; lia | psatzl R].
  psatzl R.
 rewrite hpi_rpi; auto.
 apply (precision_correct (/IZR magnifier) r_div r_sqrt r_mult); auto; lia.
repeat apply Rplus_lt_compat_r.
destruct (bound_agmpi n n1) as [_ it]; apply Rle_lt_trans with (1 := it).
clear - Rp0 n1 intp big_magnifier; unfold agmpi.
assert (1 < sqrt 2 < 15/10) by (split; approx_sqrt).
assert (lp : 0 < 4 * (2 + sqrt 2) < 14) by psatzl R.
match goal with |- ?a < _ => rewrite <- (Rinv_involutive a) end;
 [| apply Rgt_not_eq, Rmult_lt_0_compat;[psatzl R | apply exp_pos]].
apply Rinv_1_lt_contravar.
 apply (IZR_le 1),
 (fun h => Z.le_trans 1 _ _ h (Z.lt_le_incl _ _ big_magnifier)).
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
  IZR magnifier = Rpower 10 (10 ^ 6 + 4) ->
  (Rabs (hR (hpi 20) - PI) < 6/100 * Rpower 10 (-10 ^ 6))%R.
Proof using big_magnifier pos_magnifier.
intros magnifierq.
assert (nineteen1 : (1 <= 19)%nat) by lia.
assert (magnifier_10k : 100000 < IZR magnifier).
 replace 100000 with (10 * 10000) by ring.
 rewrite magnifierq, Rpower_plus, Rpower10_4.
 apply Rmult_lt_compat_r;[psatzl R | ].
 pattern 10 at 1; rewrite <- (Rpower_1 10);[ |psatzl R].
 apply Rpower_lt; psatzl R.
assert (prem : 600 * INR (19 + 1) < IZR magnifier < Rpower 531 (2 ^ 19)/14).
   split; [simpl; psatzl R | rewrite magnifierq].
  unfold Rdiv; rewrite <- (exp_ln 14);[ | psatzl R].
  rewrite <- exp_Ropp; unfold Rpower; rewrite <- exp_plus.
  apply exp_increasing, ln_lt_inv;[interval | interval | interval].
apply Rlt_trans with (1 := integer_pi 19 nineteen1 prem).
replace (21 * INR (19 + 1) + 3) with 423 by (simpl; ring).
rewrite magnifierq, Rpower_plus; try psatzl R.
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
  IZR magnifier = Rpower 10 (10 ^ 5 + 4) ->
  (Rabs (hR (hpi 17) - PI) < 5/100 * Rpower 10 (-10 ^ 5))%R.
Proof using big_magnifier pos_magnifier.
intros magnifierq.
assert (sixteen1 : (1 <= 16)%nat) by lia.
assert (magnifier_10k : 100000 < IZR magnifier).
 replace 100000 with (10 * 10000) by ring.
 rewrite magnifierq, Rpower_plus, Rpower10_4.
 apply Rmult_lt_compat_r;[psatzl R | ].
 pattern 10 at 1; rewrite <- (Rpower_1 10);[ |psatzl R].
 apply Rpower_lt; psatzl R.
assert (prem : 600 * INR (16 + 1) < IZR magnifier < Rpower 531 (2 ^ 16)/14).
   split; [simpl; psatzl R | rewrite magnifierq].
  unfold Rdiv; rewrite <- (exp_ln 14);[ | psatzl R].
  rewrite <- exp_Ropp; unfold Rpower; rewrite <- exp_plus.
  apply exp_increasing, ln_lt_inv;[interval | interval | interval].
apply Rlt_trans with (1 := integer_pi 16 sixteen1 prem).
replace (21 * INR (16 + 1) + 3) with 360 by (simpl; ring).
rewrite magnifierq, Rpower_plus; try psatzl R.
unfold Rdiv; rewrite (Rmult_comm (Rpower 10 (10 ^ 5))), Rinv_mult_distr;
  try apply Rgt_not_eq, exp_pos.
assert (0 < / Rpower 10 (10 ^ 5)).
 rewrite <- Rpower_Ropp; apply exp_pos.
rewrite Rpower_Ropp, Rpower10_4; psatzl R.
Qed.

Lemma integer_pi_othree :
  IZR magnifier = Rpower 10 (10 ^ 3 + 4) ->
  (Rabs (hR (hpi 10) - PI) < 3/100 * Rpower 10 (-10 ^ 3))%R.
Proof using big_magnifier pos_magnifier.
intros magnifierq.
assert (nine1 : (1 <= 9)%nat) by lia.
assert (magnifier_10k : 10000 < IZR magnifier).
 replace 10000 with (1 * 10000) by ring.
 rewrite magnifierq, Rpower_plus, Rpower10_4.
 apply Rmult_lt_compat_r;[psatzl R | ].
 pattern 1 at 1; rewrite <- (Rpower_O 10);[ |psatzl R].
 apply Rpower_lt; psatzl R.
assert (prem : 600 * INR (9 + 1) < IZR magnifier < Rpower 531 (2 ^ 9)/14).
   split; [simpl; psatzl R | rewrite magnifierq].
  unfold Rdiv; rewrite <- (exp_ln 14);[ | psatzl R].
  rewrite <- exp_Ropp; unfold Rpower; rewrite <- exp_plus.
  apply exp_increasing, ln_lt_inv;[interval | interval | interval].
apply Rlt_trans with (1 := integer_pi 9 nine1 prem).
replace (21 * INR (9 + 1) + 3) with 213 by (simpl; ring).
rewrite magnifierq, Rpower_plus; try psatzl R.
unfold Rdiv; rewrite (Rmult_comm (Rpower 10 (10 ^ 3))), Rinv_mult_distr;
  try apply Rgt_not_eq, exp_pos.
assert (0 < / Rpower 10 (10 ^ 3)).
 rewrite <- Rpower_Ropp; apply exp_pos.
rewrite Rpower_Ropp, Rpower10_4; psatzl R.
Qed.

Lemma integer_pi_othree_bin :
  IZR magnifier = Rpower 2 3336 ->
  (Rabs (hR (hpi 10) - PI))
     < 213 * Rpower 2 (-14) * Rpower 2 (-3322).
Proof using big_magnifier pos_magnifier.
intros magnifierq.
assert (nine1 : (1 <= 9)%nat) by lia.
assert (prem : 600 * INR (9 + 1) < IZR magnifier < Rpower 531 (2 ^ 9)/14).
  split.
    now rewrite magnifierq; unfold Rpower; simpl; interval.
  rewrite magnifierq; unfold Rpower; interval.
apply Rlt_le_trans with (1 := integer_pi _ nine1 prem).
replace (21 * INR (9 + 1) + 3) with 213 by (simpl; ring).
rewrite magnifierq.
rewrite Rmult_assoc; apply Rmult_le_compat_l;[psatzl R | ].
replace 3336 with (14 + 3322) by ring; rewrite Rpower_plus.
rewrite Rinv_mult_distr, <- !Rpower_Ropp; try (apply Rgt_not_eq, exp_pos).
apply Req_le; reflexivity.
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
  let magnifier := (10 ^ (10 ^ 6 + 4))%Z in
  let n := hpi magnifier 20 in
      (601 < n mod 10000 < 9399)%Z ->
  let n' := (n/10000)%Z in
   0 < PI - hR (10 ^ (10 ^ 6)) n' < Rpower 10 (- 10 ^ 6).
Proof.
intros pr n ctr n'.
assert (main : hR (10 ^ (10 ^ 6)) n' < PI < hR (10 ^ (10 ^ 6)) (n' + 1)).
  assert (cd : (0 < 10 ^ 4)%Z) by reflexivity.
  assert (cp : (0 < 10 ^ (10 ^ 6))%Z).
    apply Z.pow_pos_nonneg; [reflexivity | discriminate].
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
          apply Z.pow_lt_mono_l;[| compute; split;[discriminate |]]; reflexivity.
        discriminate.
      reflexivity.
    assert (cp' : (0 < 10 ^ (10 ^ 6 + 4))%Z).
      apply Z.pow_pos_nonneg; [reflexivity | compute; discriminate].
    assert (q : IZR (10 ^ (10 ^ 6 + 4)) = Rpower 10 (10 ^ 6 + 4)).
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      apply f_equal; rewrite plus_IZR.
      rewrite Zpow_Rpower, <- Rpower_pow; try psatzl R; try lia.
      apply (f_equal (fun x => Rpower 10 x + 4)); simpl; ring.
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
      replace (IZR 6) with (INR 6) at 2 by (simpl; ring).
      rewrite Rpower_pow, !Rmult_assoc, (Rmult_comm (6/100)),
      <- Rmult_assoc;[ | psatzl R].
      rewrite <- Rpower_plus, Rplus_opp_l, Rpower_O, Rmult_1_l;[ | psatzl R].
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      replace (IZR 4) with (INR 4) by (simpl; ring).
      rewrite Rpower_pow;[ | psatzl R].
      replace (10 ^ 4 * (6 / 100)) with (IZR 20 * IZR 30) by (simpl; psatzl R).
      unfold RbZ; rewrite <- mult_IZR, floor_IZR; reflexivity.
    rewrite sm.
    exact ctr.
 assert (t := rerounding_simple (10 ^ (10 ^ 6)) (10 ^ 4) (6/100 * Rpower 10 (-10 ^ 6))
             PI n cd cp t' ctr').
 exact t.
split;[apply Rlt_Rminus; tauto | destruct main as [_ main]]; revert main.
rewrite hplus_spec; unfold hR at 2; simpl (IZR 1).
unfold Rdiv; rewrite Rmult_1_l.
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
replace (IZR 6) with (INR 6) by (simpl; field).
rewrite Rpower_pow;[|psatzl R].
rewrite Rpower_Ropp; psatzl R.
Qed.

Lemma pi_ofive :
  let magnifier := (10 ^ (10 ^ 5 + 4))%Z in
  let n := hpi magnifier 17 in
      (501 < n mod 10000 < 9499)%Z ->
  let n' := (n/10000)%Z in
   0 < PI - hR (10 ^ (10 ^ 5)) n' < Rpower 10 (- 10 ^ 5).
Proof.
intros pr n ctr n'.
assert (main : hR (10 ^ (10 ^ 5)) n' < PI < hR (10 ^ (10 ^ 5)) (n' + 1)).
  assert (cd : (0 < 10 ^ 4)%Z) by (compute; reflexivity).
  assert (cp : (0 < 10 ^ (10 ^ 5))%Z).
    apply Z.pow_pos_nonneg; [reflexivity | discriminate].
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
          apply Z.pow_lt_mono_l;[| compute; split;[discriminate | ]]; reflexivity.
        discriminate.
      reflexivity.
    assert (cp' : (0 < 10 ^ (10 ^ 5 + 4))%Z).
      apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
(* funny : a bug by the user here, (replacing 5 by 6), causes a time costly computation. *)
    assert (q : IZR (10 ^ (10 ^ 5 + 4)) = Rpower 10  (10 ^ 5 + 4)).
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      apply f_equal; rewrite plus_IZR.
      rewrite Zpow_Rpower, <- Rpower_pow; try psatzl R; try lia.
      apply (f_equal (fun x => Rpower 10 x + 4)); simpl; ring.
    apply (integer_pi_ofive (10 ^ (10 ^ 5 + 4)) gt1000 cp' q).
  assert (ctr' : (Rh (10 ^ 10 ^ 5 * 10 ^ 4) (5/ 100 * Rpower 10 (- 10 ^ 5)) + 1 <
       n mod 10 ^ 4 <
       10 ^ 4 - (Rh (10 ^ 10 ^ 5 * 10 ^ 4) (5/ 100 * Rpower 10 (- 10 ^ 5)) + 1))%Z).
    assert (sm: (Rh (10 ^ 10 ^ 5 * 10 ^ 4) (5/ 100 * Rpower 10 (- 10 ^ 5)) = 500)%Z).
      unfold Rh; rewrite mult_IZR.
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      replace (IZR 5) with (INR 5) at 2 by (simpl; ring).
      rewrite Rpower_pow, !Rmult_assoc, (Rmult_comm (5/100)), <- Rmult_assoc;
        [ | psatzl R].
      rewrite <- Rpower_plus, Rplus_opp_l, Rpower_O, Rmult_1_l;[ | psatzl R].
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      replace (IZR 4) with (INR 4) by (simpl; ring).
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
replace (IZR 5) with (INR 5) by (simpl; field).
rewrite Rpower_pow;[|psatzl R].
rewrite Rpower_Ropp; psatzl R.
Qed.

(* One could probably restrict the number of extra required bits
  to be only 8 or 9, as this would be enough to do better than 213 *)
Lemma pi_othree_bin :
  let magnifier := (2 ^ 3336)%Z in
  let n := hpi magnifier 10 in
      (214 < n mod 16384 < 16170)%Z ->
  let n' := (n/2 ^ 14)%Z in
   0 < PI - hR (2 ^ 3322) n' < Rpower 2 (- 3322).
Proof.
intros pr n ctr n'.
assert (main : hR (2 ^ 3322) n' < PI < hR (2 ^ 3322) (n' + 1)).
  assert (cd : (0 < 2 ^ 14)%Z) by (compute; reflexivity).
  assert (cp : (0 < 2 ^ 3322)%Z).
    apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
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
      rewrite Zpow_Rpower;[ | | compute; discriminate]; reflexivity.
    now apply (integer_pi_othree_bin _ gt1000 cp' q).
  assert (ctr' : (Rh (2 ^ 3322 * 2 ^ 14)
                  (213 * Rpower 2 (-14) * Rpower 2 (-3322)) + 1 <
       n mod 2 ^ 14 <
       2 ^ 14 - (Rh (2 ^ 3322 * 2 ^ 14)
             (213 * Rpower 2 (-14) * Rpower 2 (-3322)) + 1))%Z).
    assert (sm: (Rh (2 ^ 3322 * 2 ^ 14) (213 * Rpower 2 (-14) * Rpower 2 (-3322)) = 
                   213)%Z).
      unfold Rh; rewrite mult_IZR.
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
      rewrite !Rmult_assoc, <- !Rpower_plus.
      match goal with |- (RbZ (_ * Rpower _ ?x) = _)%Z =>
       assert (x0 : x = 0); [ring | rewrite x0, Rpower_O, Rmult_1_r;
                 [  | psatzl R]]
      end.
      unfold RbZ; rewrite floor_IZR; reflexivity.
    rewrite sm.
    assumption.
 exact (rerounding_simple (2 ^ 3322) (2 ^ 14) _
             PI n cd cp t' ctr').
split;[apply Rlt_Rminus; tauto | destruct main as [_ main]]; revert main.
rewrite hplus_spec; unfold hR at 2; simpl (IZR 1); unfold Rdiv; rewrite Rmult_1_l.
rewrite Zpow_Rpower;[ | reflexivity | compute; discriminate].
rewrite <- Rpower_Ropp, <- IZR_Zneg; psatzl R.
Qed.

Lemma change_magnifier : forall m1 m2 x, (0 < m2)%Z ->
  (m2 < m1)%Z ->
  hR m1 x - /IZR m2 < hR m2 (x * m2/m1) <= hR m1 x.
Proof.
intros m1 m2 x p0 cmpp.
assert (0 < m1)%Z by (apply Z.lt_trans with (1 := p0) (2 :=cmpp)).
unfold hR; split.
  apply Rmult_lt_reg_r with (IZR m2); [apply (IZR_lt 0); assumption | ].
  rewrite Rmult_minus_distr_r.
  unfold Rdiv at 2; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
    [|apply Rgt_not_eq, (IZR_lt 0); assumption].
  apply Rmult_lt_reg_r with (IZR m1); [apply (IZR_lt 0); assumption | ].
  rewrite Rmult_minus_distr_r, Rmult_1_l.
  unfold Rdiv; rewrite !Rmult_assoc, (Rmult_comm (/ _)), !Rmult_assoc.
  rewrite Rinv_r, Rmult_1_r;[ | apply Rgt_not_eq, (IZR_lt 0); assumption].
  assert (help : forall x y z, x < z + y -> x - y < z) by (intros; psatzl R).
  apply help; clear help; rewrite <- !mult_IZR,  <- plus_IZR;  apply IZR_lt.
  pattern (x * m2)%Z at 1; rewrite (Z_div_mod_eq (x * m2)  (m1));
    [|apply Z.lt_gt; assumption].
  rewrite (Zmult_comm (m1)).
  apply Zplus_lt_compat_l.
  destruct (Zmod_pos_bound (x * m2) (m1)); assumption.
apply Rmult_le_reg_r with (IZR m2); [apply (IZR_lt 0); assumption | ].
  unfold Rdiv at 1; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
    [|apply Rgt_not_eq, (IZR_lt 0); assumption].
apply Rmult_le_reg_r with (IZR m1); [apply (IZR_lt 0); assumption | ].
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
  let magnifier := (2 ^ 3336)%Z in
  let n := hpi magnifier 10 in
    let n' := (n * 10 ^ (10 ^ 3 + 4) / 2 ^ 3336)%Z in
      (265 < n' mod 10 ^ 4 < 9735)%Z ->
   0 < PI - hR (10 ^ (10 ^ 3)) (n' / 10 ^ 4) < Rpower 10 (-(Rpower 10 3)).
Proof.
assert (helpring : forall b a c:R, a - c = a - b + (b - c))
          by (intros; ring).
assert (gt1000 : (1000 < 2 ^ 3336)%Z)
   by (rewrite <- Z.ltb_lt; reflexivity).
assert (p0 : (0 < 2 ^ 3336)%Z) by (rewrite <- Z.ltb_lt; reflexivity).
assert (q : IZR (2 ^ 3336) = Rpower 2 3336).
  rewrite Zpow_Rpower;[ | | compute; discriminate]; reflexivity.
assert (t := integer_pi_othree_bin (2 ^ 3336) gt1000 p0 q).
intros magnifier n n' ctr; fold magnifier in q, t.
(* fold or change did not manage to avoid heavy computation here *)
assert (t' :
 Rabs (hR magnifier n - PI) < 213 * Rpower 2 (-14) * Rpower 2 (-3322))
 by exact t; clear t.
assert (m10 : (0 < 10 ^ (10 ^ 3 + 4))%Z).
 apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
assert (cmpp : (10 ^ (10 ^ 3 + 4) < 2 ^ 3336)%Z).
 rewrite <- Z.ltb_lt; vm_compute; reflexivity.
assert (t := change_magnifier (2 ^ 3336) _ n m10 cmpp).
fold magnifier in t.
(* again, fold n' does not work here *)
assert (t'' :
   hR magnifier n - / IZR (10 ^ (10 ^ 3 + 4)) <
   hR (10 ^ (10 ^ 3 + 4)) n' <= hR magnifier n) by exact t; clear t.
(* This does not work either
replace (n * 10 ^ (10 ^ 3 + 4) / magnifier)%Z with
  n' in t;[ | unfold n', magnifier].
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
  assert (exists vp, vp = magnifier) as [vp hvp].
    eapply ex_intro; eapply refl_equal.
  rewrite <- hv.
 (* BUG: I can't do this
 replace (v - PI) with
  ((v - hR vp n) + (hR vp n - PI)) by ring. *)
  rewrite (helpring (hR magnifier n)).
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
      apply Rplus_lt_reg_r with (hR magnifier n).
      unfold Rminus; rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
      rewrite hv; rewrite Rplus_comm; destruct t'' as [it _]; exact it.
    exact t'.
  assert (0 < IZR (10 ^ (10 ^ 3 + 4))).
    apply (IZR_lt 0); apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
  apply Rmult_lt_reg_r with (IZR (10 ^ (10 ^ 3 + 4))).
    assumption.
(* Bug? here, I can't finish the rewriting wit Rmult_1_r *)
  rewrite Rmult_plus_distr_r, 3!Rmult_assoc, Rinv_l;
    [ | apply Rgt_not_eq; assumption].
 (* I have to set the instantiation precisely! *)
  rewrite (Rmult_1_r (IZR 264)).
  rewrite (Rmult_comm (Rpower 2 (-3322))
           (IZR (10 ^ (10 ^ 3 + 4)))).
  rewrite (Rmult_comm (Rpower (IZR 2) (-IZR 14))).
  rewrite <- 2!Rmult_assoc.
  apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR 14)).
    apply exp_pos.
  rewrite Rmult_plus_distr_r, !Rmult_assoc, <- Rpower_plus, Rplus_opp_l.
  rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
  apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR 3322)).
    apply exp_pos.
  rewrite Rmult_plus_distr_r, !Rmult_assoc, <- !Rpower_plus.
  rewrite <- (plus_IZR (Zneg 3322)).
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
    unfold RbZ; rewrite floor_IZR; reflexivity.
  rewrite sm; assumption.
destruct (rerounding_simple (10 ^ 10 ^ 3) (10 ^ 4)
          (264 * /IZR (10 ^ (10 ^ 3) * 10 ^ 4)) PI n' d0 k0 n'cl ctr')
   as [rrs1 rrs2].
split;[psatzl R | ].
revert rrs2; unfold hR, Rdiv; rewrite plus_IZR.
rewrite Rmult_plus_distr_r; intros rrs2.
rewrite Rlt_minus_l; apply Rlt_le_trans with (1 := rrs2).
rewrite Rplus_comm; apply Rplus_le_compat_r.
apply Req_le; clear.
rewrite Rmult_1_l, Rpower_Ropp.
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
simpl; unfold Rpower; apply exp_increasing; interval.
Qed.

Require Import Bool.

Definition million_digit_pi : bool * Z :=
  let magnifier := (2 ^ 3321942)%Z in
  let n := hpi magnifier 20 in
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
Lemma decompose_big_number_testing_ground : (332233 = 33 * 10 ^ 4 + 22 * 10 ^ 2 + 33)%Z.
Proof.
match goal with |- (?x = _)%Z =>
  let v := decompose_big_number x in
   assert (x = v)
end.
  ring.
rewrite H; ring.
Qed.

Lemma million_digit_lb_bin : (2 ^ 3321942 < 2 * 10 ^ (10 ^ 6 + 4))%Z.
Proof.
apply lt_IZR.
rewrite mult_IZR; simpl (IZR 2); rewrite <- (exp_ln 2);[ | psatzl R].
rewrite !Zpow_Rpower;[ | reflexivity | discriminate | reflexivity | discriminate ].
replace (10 ^ 6 + 4)%Z with 1000004%Z by reflexivity.
unfold Rpower; rewrite <- exp_plus; apply exp_increasing; interval.
Qed.

Lemma pi_osix :
  fst million_digit_pi = true ->
    hR (10 ^ (10 ^ 6)) (snd million_digit_pi) < PI <
    hR (10 ^ (10 ^ 6)) (snd million_digit_pi) + Rpower 10 (-(Rpower 10 6)).
Proof.
assert (main : fst million_digit_pi = true ->
         0 < PI - hR (10 ^ (10 ^ 6)) (snd million_digit_pi) <
           Rpower 10 (-(Rpower 10 6)));
  [| intros ft; apply main in ft; clear main; psatzl R].
match type of pow10million_pow2 with
  (Z.lt _  (Z.pow _ ?v)) => set (prec := v)
end.
let v := eval compute in (prec - 14)%Z in set (prec' := v).
assert
  (main : let magnifier := (2 ^ prec)%Z in
  let n := hpi magnifier 20 in
    let n' := (n * 10 ^ (10 ^ 6 + 4) / 2 ^ prec)%Z in
    ((427 <? n' mod 10 ^ 4)%Z && (n' mod 10 ^ 4 <? 9573)%Z = true) ->
   0 < PI - hR (10 ^ (10 ^ 6)) (n' / 10 ^ 4) < Rpower 10 (-(Rpower 10 6))).
  assert (helpring : forall b a c:R, a - c = a - b + (b - c)) by (intros; ring).
  assert (gt1000 : (1000 < 2 ^ prec)%Z).
    change 1000%Z with (1000 * 1)%Z.
    change prec with (10 + (prec - 10))%Z.
    rewrite Z.pow_add_r;[ | compute | compute ]; try discriminate.
    apply Z.mul_lt_mono_nonneg;[discriminate | reflexivity | discriminate| ].
    rewrite <- Z.pow_gt_1;[ reflexivity | reflexivity].
  assert (p0 : (0 < 2 ^ prec)%Z).
    apply Z.pow_pos_nonneg;[reflexivity | discriminate].
  assert (q : IZR (2 ^ prec) = Rpower 2 (IZR prec)).
    apply Zpow_Rpower;[reflexivity | compute; discriminate].
  intros magnifier n n'.
  assert (nineteen1 : (1 <= 19)%nat) by lia.
  assert (t' : 600 * INR 20 < IZR magnifier < Rpower 531 (2 ^ 19) / 14).
    split.
(* This does not work, probably because 3321929 does not seem to parse,
   even as an integer.
  replace magnifier with ((2 ^ 13 * 2 ^ 3321929)%Z);[ | ].
  I believe now that this is because there are too many potential computations
  in the hypotheses.  A clear should help (March 22, 2017)
*)
      apply Rlt_trans with (IZR (2 ^ 14)); cycle 1.
        apply IZR_lt, Z.pow_lt_mono_r; clear; compute; auto; discriminate.
      change 14%Z with (Z.of_nat 14); rewrite <- pow_IZR; simpl IZR.
      now replace (INR 20) with 20 by (simpl; ring); psatzl R.
    apply Rmult_lt_reg_r with 14;[psatzl R |unfold Rdiv ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | psatzl R].
    unfold magnifier; rewrite -> Zpow_Rpower, <- (exp_ln 14);
    try (unfold prec; lia); try psatzl R.
    unfold Rpower; rewrite <- exp_plus; apply exp_increasing.
    now unfold prec; interval.
  assert (t'' := integer_pi magnifier gt1000 p0 19 nineteen1 t'); clear t'.
  rewrite andb_true_iff, 2!Z.ltb_lt; intros ctr.
  assert (t' : Rabs (hR magnifier n - PI) <
        423 * Rpower 2 (-14) * Rpower 2 (-IZR prec'));[|clear t''].
    replace 423 with (21 * INR (19 + 1) + 3) by (simpl; ring).
    rewrite Rmult_assoc.
    replace (Rpower 2 (-14) * Rpower 2 (-IZR prec')) with (/IZR magnifier).
      exact t''.
    rewrite <- Rpower_plus, IZR_Zneg, <- Ropp_plus_distr, Rpower_Ropp.
    now unfold magnifier; rewrite <- plus_IZR, q.
(* fold or change did not manage to avoid heavy computation here *)
  assert (m10 : (0 < 10 ^ (10 ^ 6 + 4))%Z).
    apply Z.pow_pos_nonneg;[reflexivity | compute; discriminate].
  assert (cmpp : (10 ^ (10 ^ 6 + 4) < 2 ^ prec)%Z)
     by exact pow10million_pow2.
  assert (t := change_magnifier _ _ n m10 cmpp).
(* again, fold n' does not work here *)
  assert (t'' :
    hR magnifier n - / IZR (10 ^ (10 ^ 6 + 4)) <
    hR (10 ^ (10 ^ 6 + 4)) n' <= hR magnifier n) by exact t; clear t.
(* This does not work either
replace (n * 10 ^ (10 ^ 3 + 4) / magnifier)%Z with
  n' in t;[ | unfold n', magnifier].
*)
  assert (k0 : (0 < 10 ^ (10 ^ 6))%Z).
    apply Z.pow_pos_nonneg;[reflexivity | vm_compute; discriminate].
  assert (d0 : (0 < 10 ^ 4)%Z) by
    (rewrite <- Z.ltb_lt; vm_compute; reflexivity).
  assert (pwr : (10 ^ (10 ^ 6 + 4) = 10 ^ 10 ^ 6 * 10 ^ 4)%Z).
    rewrite <- Z.pow_add_r;[reflexivity | | ]; compute; discriminate.
  assert (pwr2 : hR (10 ^ 10 ^ 6 * 10 ^ 4) n' = hR (10 ^ (10 ^ 6 + 4)) n').
    rewrite pwr; reflexivity.
  assert (n'cl : Rabs (hR (10 ^ 10 ^ 6 * (10 ^ 4)) n' - PI) <
            426 * /IZR (10 ^ (10 ^ 6) * 10 ^ 4)).
    rewrite pwr2, <- pwr.
    rewrite (helpring (hR magnifier n)).
(*  assert (exists v, v = hR (10 ^ (10 ^ 6 + 4)) n') as [v hv].
   eapply ex_intro; eapply refl_equal.
  assert (exists vp, vp = magnifier) as [vp hvp].
   eapply ex_intro; eapply refl_equal.
  rewrite <- hv. *)
    apply Rle_lt_trans with (1 := Rabs_triang _ _).
    apply Rlt_trans with (/IZR (10 ^ (10 ^ 6 + 4)) +
                    423 * Rpower 2 (-14) * Rpower 2 (-IZR prec')).
      apply Rplus_lt_compat.
        assert (0 < / IZR (10 ^ (10 ^ 6 + 4))).
          apply Rinv_0_lt_compat, (IZR_lt 0).
          apply Z.pow_pos_nonneg;[reflexivity | vm_compute; discriminate].
        apply Rabs_def1.
  (* BUG? : I don't understand why psatzl R can't do this one *)
          psatzl R.
        apply Rplus_lt_reg_r with (hR magnifier n).
        unfold Rminus; rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
        destruct t'' as [it _]; exact it.
      exact t'.
    assert (0 < IZR (10 ^ (10 ^ 6 + 4))).
      now apply (IZR_lt 0); apply Z.pow_pos_nonneg;[clear|compute; discriminate].
    apply Rmult_lt_reg_r with (IZR (10 ^ (10 ^ 6 + 4)));[assumption | ].
(* Bug? here, I can't finish the rewriting wit Rmult_1_r *)
    rewrite Rmult_plus_distr_r, 3!Rmult_assoc, Rinv_l, (Rmult_1_r 426);
      [ | apply Rgt_not_eq; assumption].
    rewrite (Rmult_comm (Rpower 2 (-IZR prec')) (IZR (10 ^ (10 ^ 6 + 4)))).
    rewrite (Rmult_comm (Rpower 2 (-14))).
    rewrite <- 2!Rmult_assoc.
    apply Rmult_lt_reg_r with (Rpower 2 (IZR 14)).
      apply exp_pos.
    rewrite Rmult_plus_distr_r, !Rmult_assoc, <- Rpower_plus, IZR_Zneg, Rplus_opp_l.
    rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
    apply Rmult_lt_reg_r with (Rpower (IZR 2) (IZR prec')).
      apply exp_pos.
    rewrite Rmult_plus_distr_r, !Rmult_assoc, <- !Rpower_plus, Rplus_opp_l.
    rewrite Rpower_O, Rmult_1_r;[ |apply (IZR_lt 0); reflexivity ].
     rewrite <- !plus_IZR, <- Zpow_Rpower;
       [ | reflexivity | vm_compute; discriminate ].
    rewrite Rmult_1_l, <- !mult_IZR.
    rewrite <- plus_IZR.
    apply IZR_lt.
    assert (uq' : (14 + prec' = prec)%Z) by (rewrite <- Z.eqb_eq; vm_compute; reflexivity).
    rewrite uq'; apply Z.lt_trans with (2 * 10 ^ (10 ^ 6 + 4) + 423 * 10 ^ (10 ^ 6 + 4))%Z.
      apply Z.add_lt_mono_r.
      exact million_digit_lb_bin.
    rewrite <- Z.mul_add_distr_r; apply Z.mul_lt_mono_nonneg.
          rewrite <- Z.leb_le; vm_compute; reflexivity.
        rewrite <- Z.ltb_lt; vm_compute; reflexivity.
      apply Z.lt_le_incl, Z.pow_pos_nonneg;[| rewrite <- Z.leb_le; vm_compute]; reflexivity.
    exact pow10million_pow2.
  assert (b10pos : 0  < IZR (10 ^ 10 ^ 6 * 10 ^ 4)).
    now apply (IZR_lt 0), Z.mul_pos_pos;[apply Z.pow_pos_nonneg;
       [|discriminate] | ]; clear.
  assert (ctr' :
  (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (426 * / IZR (10 ^ 10 ^ 6 * 10 ^ 4)) + 1 <
       n' mod 10 ^ 4 <
       10 ^ 4 -
       (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (426 * / IZR (10 ^ 10 ^ 6 * 10 ^ 4)) + 1))%Z).
    assert (sm: (Rh (10 ^ 10 ^ 6 * 10 ^ 4) (426 * /IZR (10 ^ 10 ^ 6 * 10 ^ 4))
               = 426)%Z).
      unfold Rh; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
        [ | apply Rgt_not_eq; assumption].

   unfold RbZ; rewrite floor_IZR; reflexivity.
  rewrite sm; assumption.
  destruct (rerounding_simple (10 ^ 10 ^ 6) (10 ^ 4) _ PI n' d0 k0 n'cl ctr')
    as [rrs1 rrs2].
  split.
    psatzl R.
  revert rrs2; unfold hR, Rdiv; rewrite plus_IZR.
  rewrite Rmult_plus_distr_r; intros rrs2.
  rewrite Rlt_minus_l; apply Rlt_le_trans with (1 := rrs2).
  rewrite Rplus_comm; apply Rplus_le_compat_r.
  apply Req_le; clear.
  rewrite Rmult_1_l, Rpower_Ropp; apply f_equal.
  rewrite -> Zpow_Rpower;[ | reflexivity | discriminate].
  now rewrite -> Zpow_Rpower;[ | reflexivity | discriminate].
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
From Bignums Require Import BigZ.
Require rounding_big.

Local Open Scope bigZ.

Lemma hmult_morph p x y: [rounding_big.hmult p x y] = hmult [p] [x] [y].
Proof.
unfold hmult, rounding_big.hmult.
rewrite BigZ.spec_div, BigZ.spec_mul; reflexivity.
Qed.

Lemma hdiv_morph p x y: [rounding_big.hdiv p x y] = hdiv [p] [x] [y].
Proof.
unfold hdiv, rounding_big.hdiv.
rewrite BigZ.spec_div, BigZ.spec_mul; reflexivity.
Qed.

Lemma hsqrt_morph p x: [rounding_big.hsqrt p x] = hsqrt [p] [x].
Proof.
unfold hsqrt, rounding_big.hsqrt.
rewrite BigZ.spec_sqrt, BigZ.spec_mul; reflexivity.
Qed.

Lemma h2_morph p : [rounding_big.h2 p] = h2 [p].
Proof.
unfold h2, rounding_big.h2; rewrite BigZ.spec_mul; reflexivity.
Qed.

Lemma hpi_rec_morph :
 forall s p n v1 v2 v3,
   [s] = hsqrt [p] (h2 [p]) ->
   [rounding_big.hpi_rec p n s v1 v2 v3] =
   hpi_rec [p] n [s] [v1] [v2] [v3].
Proof.
intros s p n v1 v2 v3 hs; revert v1 v2 v3.
induction n as [ | n IHn]; intros v1 v2 v3.
  simpl.
  rewrite hmult_morph, BigZ.spec_add, hs, h2_morph; reflexivity.
unfold rounding_big.hpi_rec.
change ([let sy := rounding_big.hsqrt p v1 in
          let ny := rounding_big.hdiv p (p + v1) (2 * sy) in
          let nz := rounding_big.hdiv p (p + rounding_big.hmult p v2 v1)
                       (rounding_big.hmult p (p + v2) sy) in
          rounding_big.hpi_rec p n s ny nz
             (rounding_big.hmult p v3 (rounding_big.hdiv p (p + ny) (p + nz)))] =
          let sy := hsqrt [p] [v1] in
          let ny := hdiv [p] (h1 [p] + [v1]) (2 * sy) in
          let nz := hdiv [p] (h1 [p] + hmult [p] [v2] [v1])
                       (hmult [p] (h1 [p] + [v2]) sy) in
          hpi_rec [p] n [s] ny nz
             (hmult [p] [v3] (hdiv [p] (h1 [p] + ny) (h1 [p] + nz)))).
lazy zeta; rewrite IHn; clear IHn.
 rewrite !hdiv_morph, !BigZ.spec_add, !BigZ.spec_mul, !hmult_morph, !hsqrt_morph.
 rewrite hdiv_morph, !BigZ.spec_add, !hdiv_morph, !BigZ.spec_mul, !BigZ.spec_add,
  !hmult_morph, !BigZ.spec_add, hsqrt_morph; reflexivity.
Qed.

Lemma hsyz_morph p : let '(s, y, z) := rounding_big.hsyz p in
   [s] = hsqrt [p] (h2 [p]) /\ [y] = snd (fst (hsyz [p])) /\
       [z] = snd (hsyz [p]).
Proof.
unfold rounding_big.hsyz, rounding_big.hs2, hsyz, hs2.
rewrite !hdiv_morph, !BigZ.spec_add, !BigZ.spec_mul, !hsqrt_morph, h2_morph.
repeat split; reflexivity.
Qed.

Lemma hpi_morph : forall p n, [rounding_big.hpi p n]%bigZ = hpi [p]%bigZ n.
Proof.
intros p; case n as [ | n].
  simpl.
  rewrite BigZ.spec_add, h2_morph; unfold rounding_big.hs2.
  rewrite hsqrt_morph, h2_morph; reflexivity.
unfold rounding_big.hpi.
assert (tmp := hsyz_morph p); destruct (rounding_big.hsyz p) as [[s y] z].
destruct tmp as [s_m [y_m z_m]].
rewrite hpi_rec_morph;[ | assumption].
rewrite hdiv_morph, !BigZ.spec_add, s_m, y_m, z_m.
reflexivity.
Qed.

Lemma big_compute_eq : forall (p : bigZ) (q :Z) (d1 : bigZ) (d2 : Z) n,
  [p] = q -> [d1] = d2 ->
  fst (let magnifier := p in let n := rounding_big.hpi p n in
        let n' := n * d1 / p in
        let (q, r) := BigZ.div_eucl n' (10 ^ 4) in ((427 <? r) && (r <? 9573), q)) =
  fst (let magnifier := q in let n := hpi q n in
        let n' := (n * d2 / q)%Z in
        let (q, r) := Z.div_eucl n' (10 ^ 4) in
         ((427 <? r)%Z && (r <? 9573)%Z, q)) /\
  [snd (let magnifier := p in let n := rounding_big.hpi p n in
        let n' := n * d1 / p in
        let (q, r) := BigZ.div_eucl n' (10 ^ 4) in ((427 <? r) && (r <? 9573), q))] =
  snd (let magnifier := q in let n := hpi q n in
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
Proof.
destruct big_million_eq as [f s].
rewrite f, s.
(* replace here does not work: it triggers the humongous computation. *)
 assert (big : Rpower 10 (- Rpower 10 6) = /IZR (10 ^ 10 ^ 6)).
(* Here we need the clear tactic, otherwise, it again triggers a humongous
  computation.  I don't know why. *)
clear; rewrite Rpower_Ropp, !Zpow_Rpower; try (reflexivity || discriminate).
generalize pi_osix; unfold hR; rewrite big; intros tmp; exact tmp.
Qed.
