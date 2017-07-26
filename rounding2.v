Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral arcsinh.
Require Import elliptic_integral generalities agmpi rounding_big alg2.
Require Import Interval.Interval_tactic.
Require Import rounding_correct.

Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

Section rounded_operations.

Variables (e : R) (r_half : R -> R) (r_div : R -> R -> R) (r_sqrt : R -> R)
           (r_mult : R -> R -> R)(r_square : R -> R).

Hypothesis ce : 0 < e < /10000.

Hypothesis r_half_spec : forall x, 0 <= x -> x / 2 - e < r_half x <= x / 2.

Hypothesis r_mult_spec :
  forall x y, 0 <= x -> 0 <= y -> x * y - e < r_mult x y <= x * y.

Hypothesis r_div_spec :
  forall x y, (0 < y) -> x/y - e < r_div x y <= x/y.

Hypothesis r_sqrt_spec :
  forall x, 0 <= x -> sqrt x - e < r_sqrt x <= sqrt x.

Hypothesis r_square_spec :
  forall x, x ^ 2 - e < r_square x <= x ^ 2.


Lemma Rmult_le_compat' r1 r2 r3 r4 :
 0 <= r1 -> 0 <= r4 -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4.
Proof.
intros r10 r40 r12 r34.
destruct (Rle_dec 0 r3).
  now apply Rmult_le_compat; auto.
apply Rle_trans with 0;[apply Rmult_le_0_l; auto; apply Rlt_le, Rnot_le_lt; auto| ].
apply Rmult_le_pos; auto; apply Rle_trans with r1; auto.
Qed.

Lemma sumand_error_ub  u v e' h h' k :
0 <= e' <= / 1000 ->
e <= e' ->
-e' <= h <= 0 -> -e' <= h' <= 0 ->
2 * e' <= / 4 * / 2 ^ k ->
0 <= u - v <= /4 * / 2 ^ k ->
2 ^ k * r_square ((u + h) - (v + h')) <= 2 ^ k * (u - v) ^ 2 + 2 / 3 * e'.
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
apply Rle_trans with (/2 * e' + / 6 * e' + 0);[|apply Req_le; field].
rewrite !(Rmult_plus_distr_l (2 ^ k)); apply Rplus_le_compat.
  apply Rplus_le_compat;[rewrite <- Rmult_assoc | ]. 
    apply Rmult_le_compat'; try lt0.
      now apply Rmult_le_pos; lt0.
    rewrite <- Rmult_assoc; apply Rmult_le_reg_l with (/(2 ^ k * 2)); try lt0.
    rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
    now apply Rle_trans with (1 := proj2 uv), Req_le; field; lt0.
  rewrite <- pow2_abs; simpl; rewrite -> Rmult_1_r, <- Rmult_assoc.
  apply Rmult_le_compat; try now apply Rabs_le; lt0.
      now apply Rmult_le_pos; lt0.
    now apply Rabs_pos.
  apply Rmult_le_reg_l with (/2 ^ k);[lt0 | ].
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
  now apply Rabs_le; lt0.
now apply Rmult_le_0_l, Rmult_le_0_r; lt0.
Qed.

Lemma sumand_error_lb  u v e' h h' k :
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
  apply Rplus_le_compat;[rewrite <- Rmult_assoc | ]; cycle 1.
    now apply Rle_trans with 0;[| apply Rmult_le_pos;[| apply pow2_ge_0 ]];lt0.
  enough (2 ^ k * (2 * (u - v)) * (h' - h) <= /2 * e') by psatzl R.
  apply Rmult_le_compat'; try lt0.
    now apply Rmult_le_pos; lt0.
  rewrite <- Rmult_assoc; apply Rmult_le_reg_l with (/(2 ^ k * 2)); try lt0.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
  now apply Rle_trans with (1 := proj2 uv), Req_le; field; lt0.
now apply Rmult_le_compat_l;[lt0 | apply Rmult_le_compat_r; lt0].
Qed.

Lemma agm1_error e' a b h h':
  0 <= e' <= /100 -> e <= / 10 * e' -> 4/5 <= a <= 6/7 -> 4/5 <= b <= 6/7 ->
  -e' <= h <= 0 -> -e' <= h' <= 0 ->
  (a + b) / 2 - 3/2 * e' <= r_half ((a + h) + (b + h')) <= (a + b)/2.
Proof.
intros ce' cee'.
revert a b h h'.
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
intros a b h h' ca cb ch ch'.
assert (exists e1, r_half ((a + h) + (b + h')) =
                       ((a + h) + (b + h')) / 2 + e1 * e' /\
                   - /2 <= e1 <= 0) as [e1 [Q Pe1]];[| rewrite Q; clear Q].
  destruct (r_half_spec ((a + h) + (b + h'))); try psatzl R.
  exists ((r_half ((a + h) + (b + h')) - ((a + h) + (b + h')) / 2) / e').
  split;[field; psatzl R | ].
  split; apply Rmult_le_reg_r with e';[psatzl R | | psatzl R | ];
  unfold Rdiv; rewrite -> (Rmult_assoc _ (/e')), Rinv_l; psatzl R.
replace ((a + h + (b + h')) / 2) with ((a + b) / 2 + (h + h') / 2) by field.
rewrite Rplus_assoc; split.
  apply Rplus_le_compat_l.
  replace (-(3/2 * e')) with (- e' +  -/2 * e') by field.
  apply Rplus_le_compat;[psatzl R | apply Rmult_le_compat_r;lt0].
replace ((a + b) / 2) with ((a + b) / 2 + 0) at 2 by ring.
apply Rplus_le_compat_l.
assert (e1 * e' <= 0) by (apply Rmult_le_0_r; lt0); lt0.
Qed.

Lemma sum_error e' n hsm ha1 hb1 :
  e <= / 10 * e' -> 0 <= e' <= / 10 ^ (n + 4) / 2 ^ (n + 1) ->
  Rabs hsm < 3 ^ (S n) / 2 * e' ->
  - ((3 / 2) ^ n * e') <= ha1 <= 0 -> - ((3 / 2) ^ n * e') <= hb1 <= 0 ->
  Rabs
    (hsm -
     (2 ^ n *
      r_square (u_ n (/ sqrt 2) + ha1 - (v_ n (/ sqrt 2) + hb1)) -
      salamin_sumand (S n))) < 3 ^ S (S n) / 2 * e'.
Proof.
intros ee' inte' abshsm inth inth'.
assert (ls : 3 ^ S (S n) / 2 * e' = 3 ^ S n / 2 * e' + 3 ^ S n * e').
  now rewrite <- Rmult_plus_distr_r, <- tech_pow_Rmult; field.
rewrite -> ls.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_lt_le_compat; try lt0.
rewrite -> Rabs_Ropp, Rabs_minus_sym.
assert (e'bnd : 0 <= (3 / 2) ^ n * e' <= /1000).
  split;[lt0 | ].
  apply Rmult_le_reg_l with (/(3 / 2) ^ n);[lt0 | ].
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;
    [apply Rle_trans with (1 := proj2 inte')| lt0].
  unfold Rdiv; rewrite -> (Rmult_comm (/10 ^ (n + 4))).
  apply Rmult_le_compat; try lt0; cycle 1.
    apply Rle_Rinv; try lt0; replace 1000 with (10 ^ 3) by ring; apply Rle_pow.
      now lt0.
    now lia.
  apply Rle_Rinv;[lt0 | lt0 | apply Rle_trans with ((3/2) ^ (n + 1))].
    now apply Rle_pow;[lt0 | lia].
  now apply pow_incr; psatzl R.
assert (e <= (3 / 2) ^ n * e').
  apply Rle_trans with (1 := ee'); apply Rmult_le_compat_r;[lt0 | ].
  now apply Rle_trans with 1;[| apply pow_R1_Rle]; psatzl R.
assert (2 * ((3 / 2) ^ n * e') <= /4 * / 2 ^ n).
  apply Rle_trans with (2 * ((3 / 2) ^ n * (/10 ^ (n + 4) / 2 ^ (n + 1)))).
    now repeat (apply Rmult_le_compat; try lt0).
  replace (10 ^ (n + 4)) with (1000 * 10 ^ (n + 1)) by
      (rewrite -> !pow_add; ring).
  rewrite Rinv_mult_distr; try lt0; unfold Rdiv.
  rewrite !Rinv_pow; try lt0.
  rewrite -> (Rmult_assoc (/_)), <- Rpow_mult_distr, <- (Rmult_assoc _ (/_)).
  rewrite -> pow_add, pow_1, (Rmult_comm ((/_ * _) ^ _)), !Rmult_assoc,
     (Rmult_comm (_ ^ _)), !Rmult_assoc, <- Rpow_mult_distr, <- !Rmult_assoc.
  apply Rmult_le_compat; try lt0.
  now apply pow_incr; lt0.
case_eq (n =? 0).
  assert (umv : 0 < u_ 0 (/sqrt 2) - v_ 0 (/sqrt 2) < /2).
    now unfold u_, v_; simpl; split; interval.
  intros hn_is0; apply beq_nat_true in hn_is0.
  revert inth inth' e'bnd.
  rewrite hn_is0; simpl pow; rewrite -> !Rmult_1_r, !Rmult_1_l.
  intros inth inth' e'bnd.
  assert (hp : -e' <= ha1 - hb1 <= e') by lt0.
  assert (0 <= (ha1 - hb1) ^ 2 < e').
    split;[apply pow2_ge_0 | ].
    apply Rle_lt_trans with (e' ^ 2).
      rewrite <- pow2_abs.
      now apply pow_incr;split;[apply Rabs_pos | apply Rabs_le]; lt0.
    replace e' with (1 * e') at 2 by ring.
    now simpl; rewrite Rmult_1_r; apply Rmult_lt_compat_r; lt0.
  unfold salamin_sumand; simpl (1 =? 0); simpl (2 ^ _); simpl Nat.sub; lazy iota.
  rewrite !Rmult_1_l; apply Rabs_le; split.
    apply Rle_trans with
     ((u_ 0 (/sqrt 2) - v_ 0 (/sqrt 2)) ^ 2 -
     (u_ 0 (/sqrt 2) + ha1 - (v_ 0 (/sqrt 2) + hb1)) ^ 2).
      match goal with |- _ <= ?x => replace x with
        (-(2 * (u_ 0 (/sqrt 2) - (v_ 0 (/sqrt 2))) *
          (ha1 - hb1) + (ha1 - hb1) ^ 2)) by ring
      end.
      replace (3 * e') with (1 * e' + 2 * e') by ring.
      apply Ropp_le_contravar, Rplus_le_compat; try lt0.
      now apply Rmult_le_compat'; lt0.
    apply Rplus_le_compat_l, Ropp_le_contravar.
    assert (t := r_square_spec (u_ 0 (/sqrt 2) + ha1 - (v_ 0 (/sqrt 2) + hb1))).
    now lt0.
  apply Rle_trans with
     ((u_ 0 (/sqrt 2) - v_ 0 (/sqrt 2)) ^ 2 -
     ((u_ 0 (/sqrt 2) + ha1 - (v_ 0 (/sqrt 2) + hb1)) ^ 2 - e)).
    apply Rplus_le_compat_l, Ropp_le_contravar.
    assert (t := r_square_spec (u_ 0 (/sqrt 2) + ha1 - (v_ 0 (/sqrt 2) + hb1))).
    now lt0.
  match goal with |- ?x <= _ => replace x with
        (-(2 * (u_ 0 (/sqrt 2) - (v_ 0 (/sqrt 2))) *
          (ha1 - hb1) + (ha1 - hb1) ^ 2) + e) by ring
  end.
  replace (3 * e') with (1 * e' + e' + e') by ring.
  apply Rplus_le_compat;[ | lt0].
  rewrite Ropp_plus_distr.
  apply Rplus_le_compat;[ | lt0].
  rewrite -> Ropp_mult_distr_r.
  now apply Rmult_le_compat'; lt0.
intros hn_n0; apply beq_nat_false in hn_n0.
assert (0 <= u_ n (/sqrt 2) - v_ n (/sqrt 2) <= /4 * / 2 ^ n).
  split.
    now apply Rlt_le, Rlt_Rminus, v_lt_u, ints.
  assert (s24 : /4 <= /sqrt 2) by interval.
  assert (s21 : /sqrt 2 <= 1) by interval.
  assert (s2m : 1 - /sqrt 2 < 1) by interval.
  assert (t := agm_conv_speed 1 (/sqrt 2) (1 - /sqrt 2) n Rlt_0_1 s24 s21
               (Rle_refl _) s2m).
  apply Rle_trans with (1 := t); clear t.
  apply Rlt_le, ln_lt_inv;[apply pow_lt; interval | lt0 | ].
  rewrite <- Rpower_pow;[|interval].
  unfold Rpower; rewrite ln_exp.
  assert (n1 : (1 <= n)%nat) by lia.
  clear -n1; induction n1 as [ | n n1 IHn].
    now simpl; rewrite Rmult_1_r; interval.
  rewrite -> Nat.pow_succ_r, mult_INR, Rmult_assoc; simpl INR; auto with arith.
  apply Rlt_trans with (2 * ln (/4 * /2 ^ n)).
    apply Rmult_lt_compat_l;[lt0 | assumption].
  rewrite <- tech_pow_Rmult, (Rinv_mult_distr 2 (2 ^ n));[ | lt0 | lt0].
  replace (2 * ln (/ 4 * / 2 ^ n)) with 
     (ln (/4 * /2 ^ n) + ln (/4 * /2 ^ n)) by ring.
  rewrite !ln_mult; try lt0; rewrite <- !Rplus_assoc; apply Rplus_lt_compat_r.
  rewrite Rplus_assoc; apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (ln (/2) + ln (/4));[ | interval].
  apply Rplus_le_compat_r; rewrite !ln_Rinv; try lt0.
  apply Ropp_le_contravar, ln_le; try lt0.
  now replace 2 with (2 ^ 1) at 1 by ring; apply Rle_pow; try lia; lt0.
assert ((2 / 3 + 2 ^ n) * (3 / 2) ^ n <= 3 ^ S n).
  rewrite -> Rmult_plus_distr_r, <- Rpow_mult_distr.
  replace (2 * (3 / 2)) with 3 by field.
  simpl; replace (3 * 3 ^ n) with (2 * 3 ^ n + 3 ^ n) by ring.
  apply Rplus_le_compat; try lt0.
  apply Rmult_le_compat; try lt0.
  now apply pow_incr; lt0.
apply Rabs_le; split; cycle 1.
  assert (help : forall a b c, a - c <= b -> a - b <= c) by (intros; psatzl R).
  apply help; clear help.
  assert (t := sumand_error_lb (u_ n (/sqrt 2)) (v_ n (/sqrt 2))
               ((3/2) ^ n * e') ha1 hb1 n ).
  apply (fun x h7 h1 h2 h3 h4 h5 h6 => Rle_trans x _ _ h7 (t h1 h2 h3 h4 h5 h6));
   auto.
  unfold salamin_sumand; simpl (S n =? 0); lazy iota.
  replace (S n - 1)%nat with n by lia.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar; rewrite <- Rmult_assoc.
  now apply Rmult_le_compat_r; lt0.
assert (help : forall a b c,  b <= a + c -> - c <= a - b) by (intros; psatzl R).
apply help; clear help.
assert (t := sumand_error_ub (u_ n (/sqrt 2)) (v_ n (/sqrt 2))
               ((3/2) ^ n * e') ha1 hb1 n ).
apply (fun x h7 h1 h2 h3 h4 h5 h6 => Rle_trans _ _ x (t h1 h2 h3 h4 h5 h6) h7);
   auto.
unfold salamin_sumand; simpl (S n =? 0); lazy iota.
replace (S n - 1)%nat with n by lia.
apply Rplus_le_compat_l.
rewrite <- Rmult_assoc; apply Rmult_le_compat_r;[lt0 | ].
simpl; apply Rmult_le_compat; try lt0.
apply pow_incr; lt0.
Qed.

Fixpoint rsalamin_rec (n : nat)
   (a b am1 bm1 sum twopk : R) :=
  match n with
    0 => r_div (4 * r_square a) sum
  | S p => (rsalamin_rec p (r_half (a + b)) (r_sqrt (r_mult a b)) a b
            (let v := (am1 - bm1) in
            sum - (twopk * r_square v)))%R (2 * twopk)
  end.

(* A mirror function to rsalamin_rec, designed to make sure that we got
  things right. *)
Fixpoint ssalamin_rec (n : nat)
  (a b am1 bm1 sum twopk : R) :=
  match n with
    0 => (4 * a ^ 2) / sum
  | S p => ssalamin_rec p ((a + b) / 2) (sqrt (a * b)) a b
      (let v := (am1 - bm1) in
      sum - (twopk * v ^ 2)) (2 * twopk)
  end.

Lemma ssalamin_rec_step (n : nat) (a b am1 bm1 sum twopk : R) :
  ssalamin_rec (S n) a b am1 bm1 sum twopk =
  ssalamin_rec n ((a + b) / 2) (sqrt (a * b)) a b
     (sum - twopk * (am1 - bm1) ^ 2) (2 * twopk).
Proof. reflexivity.  Qed.

(* This assumes that /2 has a perfect representation, which is fair,
   and that half sums always have a perfect representation, which is
   not fair.  TODO : fix the last part. *)
Definition rsalamin (n : nat) :=
  let s2 := r_sqrt (/2) in
  let a1 := r_half (1 + s2) in
  let b1 := r_sqrt s2 in
  let twopk := 1 in
  rsalamin_rec n a1 b1 1 s2 1 twopk.

Definition ssalamin (n : nat) :=
  let s2 := / sqrt 2 in
  let a1 := (1 + s2) / 2 in
  let b1 := sqrt s2 in
  let twopk := 1 in
  ssalamin_rec n a1 b1 1 s2 1 twopk.

Lemma ssalamin_rec_correct  n p :
  (1 <= n)%nat ->
  ssalamin_rec p (u_ n (/sqrt 2)) (v_ n (/sqrt 2))
     (u_ (n - 1) (/sqrt 2)) (v_ (n - 1) (/sqrt 2))
     (1 - sum_f_R0 salamin_sumand (n - 1)) (2 ^ (n - 1)) =
  salamin_formula (p + n).
Proof.
revert n; induction p;[reflexivity | ].
intros n n1; rewrite ssalamin_rec_step.
replace (S p + n)%nat with (p + S n)%nat by ring.
rewrite <- IHp, <- u_step, <- v_step; try lia.
replace (S n - 1)%nat with n by lia.
replace (1 - sum_f_R0 salamin_sumand n) with
 (1 - sum_f_R0 salamin_sumand (n - 1) -
   2 ^ (n - 1) *
   (u_ (n - 1) (/sqrt 2) - v_ (n - 1) (/sqrt 2)) ^ 2).
  replace (2 ^ n) with (2 * 2 ^ (n - 1)); cycle 1.
    now replace n with (S (n - 1)) at 2 by lia.
  reflexivity.
replace (sum_f_R0 salamin_sumand n) with
  (sum_f_R0 salamin_sumand (S (n - 1))); cycle 1.
  now replace (S (n - 1)) with n by lia.
rewrite tech5.
assert (help : forall x y z, x - (y + z) = x - y - z) by (intros; ring).
rewrite help; apply f_equal; unfold salamin_sumand.
simpl (S (n - 1) =? 0)%nat; lazy iota.
now replace (S (n - 1) - 1)%nat with (n - 1)%nat  by lia.
Qed.

Lemma ssalamin_correct n :
  ssalamin n = salamin_formula (n + 1).
Proof.
unfold ssalamin.
replace (sqrt (/sqrt 2)) with (v_ 1 (/sqrt 2)) by
  (now unfold v_; simpl; rewrite Rmult_1_l).
rewrite [X in ssalamin_rec _ _ _ _ _ X]
         (_ : _ = 1 - sum_f_R0 salamin_sumand (1 - 1)); cycle 1.
  now unfold salamin_sumand; simpl; rewrite Rminus_0_r.
now apply (ssalamin_rec_correct 1 n).
Qed.

Lemma agm2_error e' u v h h' :
  4/5 <= u <= 6/7 ->
  4/5 <= v <= 6/7 ->
  0 <= e' <= /100 ->
  e <= /10 * e' ->
  -e' <= h <= 0 -> -e' <= h' <= 0 ->
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
  destruct (r_mult_spec (u + h) (v + h')); try psatzl R.
  exists ((r_mult (u + h) (v + h') - (u + h) * (v + h')) / e').
  split;[field; psatzl R | ].
  now split; apply Rmult_le_reg_r with e';[psatzl R | | psatzl R | ];
  unfold Rdiv; rewrite -> (Rmult_assoc _ (/e')), Rinv_l; psatzl R.
assert (exists e2, r_sqrt ((u + h) * (v + h') + e1 * e') =
                       sqrt ((u + h) * (v + h') + e1 * e') + e2 * e' /\
                   - /10 <= e2 <= 0) as [e2 [Q Pe2]];[| rewrite Q; clear Q].
  destruct (r_sqrt_spec((u + h) * (v + h') + e1 * e')). 
    apply Rle_trans with ((3/4) * (3/4) + (-/10) * /100);[psatzl R | ].
    apply Rplus_le_compat.
      now apply Rmult_le_compat; psatzl R.
    replace e1 with (- - e1) by ring; rewrite <- 2!Ropp_mult_distr_l.
    now apply Ropp_le_contravar, Rmult_le_compat; lt0.
  exists ((r_sqrt ((u + h) * (v + h') + e1 * e') -
              sqrt ((u + h) * (v + h') + e1 * e')) / e').
  split;[field; psatzl R | ].
  now split; apply Rmult_le_reg_r with e';[psatzl R | | psatzl R | ];
  unfold Rdiv; rewrite -> (Rmult_assoc _ (/e')), Rinv_l; psatzl R.
split; cycle 1.
  apply Rle_trans with ((sqrt (u * v + 0)) + e2 * e').
    assert (-/100 <= h <= 0) by psatzl R.
    assert (-/100 <= h' <= 0) by psatzl R.
    apply Rplus_le_compat_r, sqrt_le_1;[interval | interval | ].
    replace ((u + h) * (v + h')) with 
        ((u * v) + (u + h) * h' + v * h) by ring.
    now rewrite !Rplus_assoc; apply Rplus_le_compat_l; interval.
  rewrite <- (Rplus_0_r (sqrt (u * v))); apply Rplus_le_compat.
    now rewrite Rplus_0_r; apply Req_le.
  enough (0 <= -(e2 * e')) by psatzl R.
  now rewrite Ropp_mult_distr_l; apply Rmult_le_pos; psatzl R.
replace (sqrt (u * v) - 3/2 * e') with
   (sqrt (u * v) - 7/5 * e' - /10 * e') by field.
apply Rplus_le_compat;
  [|rewrite Ropp_mult_distr_l; apply Rmult_le_compat_r;lt0].
assert (sf : ((u + h) * (v + h') + e1 * e' =
          u * v + h' * (u + h) + h * v + e1 * e')) by ring.
assert (cmp : (u + h) * (v + h') + e1 * e' <= u * v).
  replace (u * v) with (u * v + 0) by ring.
  rewrite -> sf, !Rplus_assoc; apply Rplus_le_compat_l.
  assert (0 < u + h) by psatzl R.
  assert (help : forall a, 0 <= -a -> a <= 0) by (intros; psatzl R); apply help.
  rewrite -> !Ropp_plus_distr, !Ropp_mult_distr_l.
  apply Rplus_le_le_0_compat.
    now apply Rmult_le_pos; psatzl R.
  now apply Rplus_le_le_0_compat; apply Rmult_le_pos; psatzl R.
assert (mnh : Rmin (u * v) ((u + h) * (v + h') + e1 * e') =
                    ((u + h) * (v + h') + e1 * e')).
   now rewrite Rmin_right; lt0.
assert (mxh : Rmax (u * v) ((u + h) * (v + h') + e1 * e') = u * v).
   now rewrite Rmax_left; lt0.
assert ( -/100 <= h <= 0) by psatzl R.
assert ( -/100 <= h' <= 0) by psatzl R.
assert ( 0 <= e' <= /100) by psatzl R.
set (a0 := Rmin (u * v) ((u + h) * (v + h') + e1 * e')).
set (b0 := Rmax (u * v) ((u + h) * (v + h') + e1 * e')).
assert (0 < a0) by (unfold a0; rewrite mnh; interval).
assert (ds' : forall x, a0 <= x <= b0 -> 
           is_derive sqrt x ((fun y => 1 / (2 * sqrt x)) x)).
  now intros x intx; auto_derive;[| field]; lt0.
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
now interval.
Qed.

Lemma cmp_3half_3 n : (1 <= n)%nat -> (3 / 2) ^ n <= 3 ^ n / 2.
Proof.
induction 1;[psatzl R | ].
simpl; replace (3 * 3 ^ m / 2) with (3 * (3 ^ m / 2)) by field.
apply Rmult_le_compat; try psatzl R.
apply pow_le; psatzl R.
Qed.

Lemma rsalamin_rec_correct n p a b am1 bm1 sum twopk ha hb ha1 hb1 hsm local_e :
  (1 <= n)%nat ->
  a = u_ n (/sqrt 2) + ha -> b = v_ n (/sqrt 2) + hb ->
  am1 = u_ (n - 1) (/sqrt 2) + ha1 -> bm1 = v_ (n - 1) (/sqrt 2) + hb1 ->
  sum = 1 - sum_f_R0 salamin_sumand (n - 1) + hsm ->
  twopk = 2 ^ (n - 1) ->
  - (3 / 2) ^ n * local_e <= ha <= 0 ->
  - (3 / 2) ^ n * local_e <= hb <= 0 ->
  - (3 / 2) ^ (n - 1) * local_e <= ha1 <= 0 ->
  - (3 / 2) ^ (n - 1) * local_e <= hb1 <= 0 ->
  Rabs hsm < 3 ^ n / 2 * local_e ->
  0 <= local_e <= / 10 ^ (n + p + 4) / 3 ^ (n + p) ->
  10 * e <= local_e ->
  Rabs (rsalamin_rec p a b am1 bm1 sum twopk - salamin_formula (p + n)) <= 
   16 * (3 / 2) ^ (p + n) * local_e + 8 * 3 ^ (p + n) * local_e + 10 * local_e.
Proof.
revert n a b am1 bm1 sum twopk ha hb ha1 hb1 hsm local_e.
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
  intros n a b am1 bm1 sum twopk ha hb ha1 hb1 hsm local_e n1 aq bq a1q b1q sq tq
   intha inthb inta1 intb1 intsm inte clee.
  assert (nm1 : n = ((n - 1) + 1)%nat) by lia.
  clear inthb inta1 intb1.
  rewrite Nat.add_0_l.
  assert (bn :  3 ^ n / 2 * (/10 ^ (n + 0 + 4) / 3 ^ (n + 0)) < /100).
    replace 100 with (Rpower 10 2); cycle 1.
      now replace 100 with (10 ^ 2) by ring; rewrite <- Rpower_pow; auto; lt0.
    assert (0 < Rpower 10 2) by (unfold Rpower; lt0).
    rewrite Nat.add_0_r; field_simplify; try split; try lt0.
    unfold Rdiv; rewrite -> !Rmult_1_l. 
    rewrite  <- (Rpower_1 2) at 1; try lt0.
    rewrite <- Rpower_pow; try lt0; unfold Rpower.
    rewrite <- exp_plus, <- !exp_Ropp; apply exp_increasing.
    assert (0 < ln 2) by interval; assert (0 < ln 10) by interval.
    rewrite plus_INR; replace (INR 4) with 4 by (simpl; ring).
    rewrite Rmult_plus_distr_r; enough (0 <= n * ln 10) by lt0.
    now apply Rmult_le_pos; try lt0; apply pos_INR.
  assert (ihsm : -/100 <= hsm <= /100).
    apply Fcore_Raux.Rabs_le_inv, Rlt_le, Rlt_trans with (1 := intsm).
    apply Rle_lt_trans with (3 ^ n/2 * (/10 ^ (n + 0 + 4) / 3 ^ (n + 0))); auto.
    apply Rmult_le_compat_l; try lt0; cycle 1.
(* using intha here. *)
  assert (bha : -/100 < ha).
    apply Rlt_le_trans with (2 := proj1 intha).
    rewrite <- Ropp_mult_distr_l; apply Ropp_lt_contravar.
    apply Rle_lt_trans with (3 ^ n / 2 * local_e).
      now apply Rmult_le_compat_r;[lt0 | apply cmp_3half_3].
    apply Rle_lt_trans with (3 ^ n/2 * (/10 ^ (n + 0 + 4) / 3 ^ (n + 0))); auto.
    now apply Rmult_le_compat_l;lt0.
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
  rewrite help; apply Rle_trans with (1 := Rabs_triang _ _).
  replace (16 * (3 / 2)  ^ n * local_e + 8 * 3 ^ n * local_e + 10 * local_e)
   with
   (4 * ((2 * ((3 / 2) ^ n * local_e)) * 2) + 8 * 3 ^ n * local_e + 1 * local_e + 
     8 * local_e + 1 * local_e)
     by ring.
  apply Rplus_le_compat; cycle 1.
    rewrite -> Rabs_mult, (Rabs_right e);[ | lt0].
(* loosing the advantage of having e less than 1/10 local_e here. *)
    apply Rle_trans with (Rabs e2 * (10 * e)).
      now apply Rmult_le_compat_l;[lt0 | lt0].
    apply Rmult_le_compat; try lt0.
    now apply Rabs_le; lt0.
  rewrite -> Rmult_plus_distr_l, Rdiv_plus_distr, help.
  assert (ssub := salamin_sum_ub (n - 1)).
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat; cycle 1.
    assert (/ (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) < 2).
      rewrite <- (Rinv_involutive 2); try lt0; apply Rinv_lt_contravar.
        apply Rmult_lt_0_compat; try lt0.
      now assert (t := salamin_sum_ub (n -1)); lt0.
    replace (8 * local_e) with (4 * local_e * 2) by ring.
    rewrite Rabs_left1; cycle 1.
      apply Rmult_le_0_r;[apply Rmult_le_0_l | ]; try lt0.
      now apply Rmult_le_0_r; lt0.
    apply Rle_trans with
        (4 * e * / (1 - sum_f_R0 salamin_sumand (n - 1) + hsm)).
      unfold Rdiv; rewrite !(Ropp_mult_distr_l (4 * (e1 * e))).
      apply Rmult_le_compat_r;[lt0 | ].
        rewrite -> Ropp_mult_distr_r, Ropp_mult_distr_l.
      apply Rmult_le_compat_l;[lt0 | ].
      now rewrite <- (Rmult_1_l e) at 2; apply Rmult_le_compat_r; lt0.
    apply Rle_trans with
        (4 * local_e / (1 - sum_f_R0 salamin_sumand (n - 1) + hsm)).
      now apply Rmult_le_compat_r; lt0.
(* again loosing the advantage of having e less than 1/10 local_e here. *)
    now apply Rmult_le_compat_l; lt0.
  replace ((u_ n (/ sqrt 2) + ha) ^ 2) with
          (u_ n (/ sqrt 2) ^ 2 + (2 * u_ n (/ sqrt 2) * ha + ha ^ 2)) by ring.
  rewrite -> Rmult_plus_distr_l, Rdiv_plus_distr.  
  assert (hel2 : forall a b c, a + b - c = b + (a - c)) by (intros; ring).
  rewrite hel2; clear hel2.
  apply Rle_trans with (1 := Rabs_triang _ _).
  assert (t := u_v_s2_bound (n - 1)); rewrite <- nm1 in t.
  rewrite Rplus_assoc; apply Rplus_le_compat.
    assert (hel2 : forall a b c, a * b / c = a * (b / c)) by
      (intros; unfold Rdiv; ring).
    rewrite -> hel2, Rabs_mult, (Rabs_right 4); try lt0.
    unfold Rdiv; rewrite -> Rabs_mult.
    apply Rmult_le_compat_l;[lt0 | ].
    apply Rmult_le_compat;[lt0 | lt0 | |].
      apply Rle_trans with (2 * (Rabs (u_ n (/sqrt 2) * ha))).
        rewrite Rabs_left1; cycle 1.
          replace (2 * u_ n (/sqrt 2) * ha + ha ^ 2) with
             ((2 * u_ n (/sqrt 2) + ha) * ha) by ring.
          now apply Rmult_le_0_l; lt0.
        rewrite Rabs_left1; cycle 1.
          now apply Rmult_le_0_l; lt0.
        rewrite <- Ropp_mult_distr_r; apply Ropp_le_contravar.
        assert (0 <= ha ^ 2) by apply pow2_ge_0; rewrite Rmult_assoc.
        now psatzl R.
      apply Rmult_le_compat_l;[lt0|].
      rewrite -> Rabs_mult, Rabs_right;[|lt0].
      rewrite Rabs_left1;[ | lt0].
      apply Rle_trans with (6/7 * - ha).
        now apply Rmult_le_compat_r; lt0.
(* using intha here. *)
      change (3 * / 2) with (3/2); rewrite <- Ropp_mult_distr_l in intha.
      assert (int : -ha <= ((3 / 2) ^ n * local_e)).
        now rewrite <- (Ropp_involutive (_ * _)); apply Ropp_le_contravar; tauto.
      clear intha.
      apply Rle_trans with (6/7 * ((3 / 2) ^ n * local_e)).
        apply Rmult_le_compat_l;[lt0 | auto].
      assert (0 < (3 / 2) ^ n * local_e) by lt0; psatzl R.
    rewrite Rabs_right;[|  apply Rle_ge, Rlt_le; lt0].
    now rewrite <- (Rinv_involutive 2);[|lt0]; apply Rinv_le_contravar; lt0.
  unfold salamin_formula; set (B := 1 - _); set (A := 4 * _).
  replace (A / (B + hsm) - A / B) with (- A * hsm / (B * (B + hsm))); cycle 1.
    now field; split; unfold B; psatzl R.
  unfold Rdiv; rewrite <- !Ropp_mult_distr_l, Rabs_Ropp.
(* TODO : 16 here could easily be 9. *)
  apply Rle_trans with (16 * (3 ^ n / 2 * local_e)).
    rewrite -> (Rmult_comm A), (Rmult_assoc hsm), (Rmult_comm hsm).
    rewrite Rabs_mult; apply Rmult_le_compat; try lt0.
    apply Rle_trans with (Rabs A * 4); cycle 1.
(* A can be shown to be less than 3, and /(B * (B + hsm)) can also be shown
   to be less than 3. *)
      replace 16 with (4 * 4) by ring.
      rewrite Rabs_mult; apply Rmult_le_compat_r; try psatzl R.
      rewrite Rabs_pos_eq; try psatzl R.
      pattern 4 at 2; replace 4 with (4 * 1) by ring.
      apply Rmult_le_compat_l; try psatzl R.
      rewrite Rabs_pos_eq;[ | apply pow2_ge_0].
      pattern 1 at 3; replace 1 with (1 * 1) by ring.        
      now simpl; rewrite Rmult_1_r; apply Rmult_le_compat; auto; psatzl R.
    rewrite Rabs_mult; apply Rmult_le_compat_l; try lt0.
    rewrite Rabs_Rinv; cycle 1.
      now apply Rgt_not_eq, Rmult_lt_0_compat; unfold B; psatzl R.
    assert (6 / 10 < Rabs B).
      now unfold B; rewrite Rabs_pos_eq; psatzl R.
    assert (59/100 < Rabs (B + hsm)).
      now unfold B; rewrite Rabs_pos_eq; psatzl R.
    rewrite -> Rabs_mult, Rinv_mult_distr; try psatzl R.
    apply Rmult_le_compat; try lt0.
      replace 2 with (/ / 2) by field.          
      now apply Rinv_le_contravar; lt0.
    replace 2 with (/ / 2) by field.          
    now apply Rinv_le_contravar; lt0.
  now psatzl R.
(* End of base case here. *)
intros n a b am1 bm1 sum twopk ha hb ha1 hb1 hsm local_e n1 qa qb qu qv qs
  qtp intha inthb intha1 inthb1 abshsm inte clee.
simpl rsalamin_rec.
assert (nm1 : n = ((n - 1) + 1)%nat) by lia.
assert (vub := u_v_s2_bound (n - 1)); rewrite <- nm1 in vub.
set (ha' := r_half (a + b) - u_ (S n) (/sqrt 2)).
set (e' := (3 / 2) ^ n * local_e).
assert (cmpee' : e <= /10 * e').
  unfold e'; apply Rmult_le_reg_l with 10;[lt0 | ].
  rewrite <- (Rmult_assoc 10), Rinv_r, Rmult_1_l; [ | lt0].
  apply Rle_trans with (1 * local_e);[lt0 | ].
  apply Rmult_le_compat_r; [lt0 | ].
  now apply pow_R1_Rle; psatzl R.
assert (bnde' : 0 <= e' <= /100).
  split;[unfold e'; lt0 | ].
  apply Rle_trans with (/10 ^ (n + S p + 4)); cycle 1.
    apply Rinv_le_contravar;[psatzl R | ].
    replace 100 with (1 * 100) by ring.
    rewrite pow_add; apply Rmult_le_compat; try psatzl R.
    now apply pow_R1_Rle; psatzl R.
  unfold e'; rewrite <- (Rmult_comm local_e).
  apply (Rmult_le_reg_r (/ (3 / 2) ^ n)).
    now lt0.
  rewrite -> Rmult_assoc, Rinv_r, Rmult_1_r;[ |lt0 ].
  apply Rle_trans with (1 := proj2 inte).
  apply Rmult_le_compat_l;[lt0 | ].
  apply Rinv_le_contravar;[lt0 | ].
  apply Rle_trans with (3 ^ n).
    now apply pow_incr; psatzl R.
  now apply Rle_pow;[lt0 | lia].
assert (cv : 4 / 5 <= v_ n (/sqrt 2) <= 6 / 7) by lt0.
assert (cu : 4 / 5 <= u_ n (/sqrt 2) <= 6 / 7) by lt0.
assert (intha' : - (3 / 2) ^ S n * local_e <= ha' <= 0).
  unfold ha'; rewrite u_step.
  rewrite <- Ropp_mult_distr_l in intha; rewrite <- Ropp_mult_distr_l in inthb.
  assert (tmp := agm1_error e' (u_ n (/sqrt 2))
           (v_ n (/sqrt 2)) ha hb bnde' cmpee'
           cu cv intha inthb);
   rewrite <- qa, <- qb in tmp.
  split; [ | psatzl R].
  replace (-(3 / 2) ^ S n * local_e) with (- (3 / 2 * e'))
    by now simpl; unfold e'; ring.
  psatzl R.
set (hb' := r_sqrt (r_mult a b) - v_ (S n) (/sqrt 2)).
assert (help5 : forall a b, 0 < a -> 0 < b -> -(10 * a * b) <= - a * b).
  intros x y x0 y0; rewrite <- Ropp_mult_distr_l; apply Ropp_le_contravar.
  assert (0 <= x * y) by lt0.
  now rewrite Rmult_assoc; psatzl R.
assert (intha_e' : -e' <= ha <= 0).
  split;[ | exact (proj2 intha)].
  apply Rle_trans with (2 := proj1 intha).
  now rewrite <- Ropp_mult_distr_l; apply Req_le.
assert (inthb_e' : -e' <= hb <= 0).
  split;[ | exact (proj2 inthb)].
  apply Rle_trans with (2 := proj1 inthb).
  now rewrite <- Ropp_mult_distr_l; apply Req_le.
assert (inthb' : - (3 / 2) ^ S n * local_e <= hb' <= 0).
  assert (tmp := agm2_error e' (u_ n (/sqrt 2)) (v_ n (/sqrt 2)) ha hb
          cu cv bnde' cmpee' intha_e'
          inthb_e').
  unfold hb'; rewrite v_step; split; cycle 1.
    now revert tmp; rewrite <- qa, <- qb; intros tmp; lt0.
  replace (- (3 / 2) ^ S n * local_e) with (-(3/2) * e'); cycle 1.
    now unfold e'; simpl; rewrite <- !Ropp_mult_distr_l, <- !Rmult_assoc.
  now rewrite <- qa, <-qb in tmp; lt0.
assert (np1 : (1 <= S n)%nat) by lia.
assert (qa' : r_half (a + b) = u_ (S n) (/ sqrt 2) + ha') by (unfold ha'; ring).
assert (qb' : r_sqrt (r_mult a b) = v_ (S n) (/ sqrt 2) + hb')
    by (unfold hb'; ring).
assert (qa_2 : a = u_ (S n - 1) (/sqrt 2) + ha).
  now simpl; rewrite Nat.sub_0_r.
assert (qb_2 : b = v_ (S n - 1) (/sqrt 2) + hb).
  now simpl; rewrite Nat.sub_0_r.
set (sum' := sum - twopk * r_square (am1 - bm1)).
assert (qtp' : 2 * twopk = 2 ^ (S n - 1)).
  rewrite qtp; simpl; rewrite Nat.sub_0_r.
  now change (2 ^ (S (n - 1)) = 2 ^ n); replace (S (n - 1)) with n by lia.
set (hsm' := sum' - (1 - sum_f_R0 salamin_sumand (S n - 1))).
assert (sum'q : sum' = 1 - sum_f_R0 salamin_sumand (S n - 1) + hsm').
  by now unfold hsm'; ring.
set (e'' := (3 / 2) ^ (S n - 1) * local_e).
assert (e'e'' : e' = e'').
  now unfold e', e''; simpl; rewrite Nat.sub_0_r.
assert (intha_e'' :
         - (3 / 2) ^ (S n - 1) * local_e <= ha <= 0).
  now rewrite <- Ropp_mult_distr_l; fold e''; rewrite <- e'e''.
assert (inthb_e'' :
         - (3 / 2) ^ (S n - 1) * local_e <= hb <= 0).
  now rewrite <- Ropp_mult_distr_l; fold e''; rewrite <- e'e''.
assert (IHp' := fun h1 h2 =>
         IHp _ _ _ a b sum' (2 * twopk) ha' hb' ha hb _ local_e
         np1 qa' qb' qa_2 qb_2 sum'q qtp' intha' inthb' intha_e'' inthb_e'' h1 h2
         clee).
replace (S p + n)%nat with (p + S n)%nat by ring.
apply IHp'; cycle 1.
  move inte after IHp'.
  now replace (S n + p)%nat with (n + S p)%nat by ring.

enough (cmphsm' : Rabs hsm' < 3 ^ S n / 2 * local_e) by auto.
unfold hsm', sum'.
assert (inte_1 : 0 <= local_e <= / 10 ^ (n + 3) / 2 ^ n).
  split;[exact (proj1 inte) | apply Rle_trans with (1 := proj2 inte)].
  apply Rmult_le_compat; try lt0.
    apply Rinv_le_contravar; try lt0.
    now apply Rle_pow; try lt0; lia.
  apply Rinv_le_contravar; try lt0; apply Rle_trans with (3 ^ n).
    now apply pow_incr; lt0.
  now apply Rle_pow; try lt0; lia.
assert (inte_2 : 0 <= local_e <= / 10 ^ (S n + 3) / 2 ^ S n).
  split;[exact (proj1 inte) | apply Rle_trans with (1 := proj2 inte)].
  apply Rmult_le_compat; try lt0.
    apply Rinv_le_contravar; try lt0.
    now apply Rle_pow; try lt0; lia.
  apply Rinv_le_contravar; try lt0; apply Rle_trans with (3 ^ S n).
    now apply pow_incr; lt0.
  now apply Rle_pow; try lt0; lia.
assert (clee' : e <= /10 * local_e) by lt0.
rewrite <- Ropp_mult_distr_l in intha1.
rewrite <- Ropp_mult_distr_l in inthb1.
rewrite -> qtp, qu, qv.  
assert (hel2 : forall x y z t, (1 - z + x) - y - (1 - (z + t)) = x - (y - t)).
  now intros; ring.
replace (S n - 1)%nat with (S (n - 1)) by lia.
rewrite -> qs, tech5, hel2.
assert (tmp := sum_error local_e (n - 1) hsm ha1 hb1 clee').
replace (S n) with (S (S (n - 1))) by lia.
apply tmp; auto.
  replace (n - 1 + 4)%nat with (n + 3)%nat by lia.
  now replace (n - 1 + 1)%nat with n by lia.
now replace (S (n - 1)) with n by lia.
Qed.

Lemma rsalamin_correct (n : nat) :
 0 <= e <= / 10 ^ (n + 6) / 3 ^ (n + 1) ->
  Rabs (rsalamin n - salamin_formula (n + 1)) <=
  (160 * (3 / 2) ^ (n + 1) + 80 * 3 ^ (n + 1) + 100) * e.
Proof.
intros ce'; unfold rsalamin.
assert (t := rsalamin_rec_correct 1 n (r_half (1 + r_sqrt (/ 2)))
              (r_sqrt (r_sqrt (/ 2))) 1
              (r_sqrt (/ 2)) 1 1 
              (r_half (1 + r_sqrt (/ 2)) - u_ 1 (/sqrt 2))
              (r_sqrt (r_sqrt (/ 2)) - v_ 1 (/sqrt 2))
              0 (r_sqrt (/ 2) - (/sqrt 2)) 0 (10 * e)).
replace ((160 * (3 / 2) ^ (n + 1) + 80 * 3 ^ (n + 1) + 100) * e) with
(16 * (3 / 2) ^ (n + 1) * (10 * e) + 8 * 3 ^ (n + 1) * (10 * e) +
      10 * (10 * e)) by ring.
assert (Rabs 0 < 3 ^ 1 / 2 * (10 * e)).
  now rewrite Rabs_R0; lt0.
assert (0 <= 10 * e <= / (10 * 10 ^ (n + 4)) / (3 * 3 ^ n)).
  split;[lt0 | ]. 
  apply Rmult_le_reg_l with (/10); try lt0.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;[ | lt0].
  apply Rle_trans with (1 := proj2 ce').
  unfold Rdiv; rewrite <- Rmult_assoc.
  apply Rmult_le_compat; try lt0.
    rewrite <- Rinv_mult_distr; try lt0; apply Rinv_le_contravar; try lt0.
    now rewrite !pow_add; apply Req_le; ring.
  now apply Rinv_le_contravar; try lt0; apply Req_le; rewrite !pow_add; ring.
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
assert (exists e1, r_sqrt (/2) = sqrt (/2) + e1 * e /\ -1 <= e1 <= 0)
          as [e1 [Qe1 Pe1]].
  destruct (r_sqrt_spec (/2)); try psatzl R.
  eapply ex_intro;split;[eapply help4, refl_equal | ].
    lt0.
  now split;[apply help1 | apply help2]; psatzl R.
assert (interval_weakness : 0 <= e <= /10000) by lt0.
assert (- (3/2) * (10 * e) <= r_half (1 + r_sqrt (/2)) - u_ 1 (/ sqrt 2) <= 0).
  rewrite Qe1.
  assert (exists e2, r_half (1 + (sqrt(/2) + e1 * e)) =
           (1 + (sqrt(/2) + e1 * e)) / 2 + e2 * e /\ -1 <= e2 <= 0) as
       [e2 [Q Pe2]];[| rewrite Q; clear Q].
    destruct (r_half_spec (1 + (sqrt(/2) + e1 * e))); try psatzl R.
      now interval.
    eapply ex_intro;split;[eapply help4, refl_equal; lt0 | ].
    now split;[apply help1 | apply help2]; lt0.
  unfold u_; simpl.
  replace ((1 + (sqrt (/2) + e1 * e)) / 2 + e2 * e - (1 + / sqrt 2) / 2) with
     (e1 / 2 * e + e2 * e) by now rewrite inv_sqrt; lt0.
   rewrite <- Rmult_plus_distr_r; split;[ | apply Rmult_le_0_r; lt0].
   now rewrite <- Rmult_assoc; apply Rmult_le_compat_r; lt0.
assert (- (3 / 2) * (10 * e) <= r_sqrt (r_sqrt (/ 2)) - v_ 1 (/ sqrt 2) <= 0).
  rewrite Qe1.
  assert (exists e2, r_sqrt (sqrt (/2) + e1 * e) =
     sqrt (sqrt (/2) + e1 * e) + e2 * e /\ -1 <= e2 <= 0)
            as [e2 [Q Pe2]];[| rewrite Q; clear Q].
    destruct (r_sqrt_spec (sqrt (/2) + e1 * e)); try psatzl R.

       apply Rle_trans with (/2 + (-1 * / 2));[lt0 | ].
      apply Rplus_le_compat; [interval | ].
      apply Rle_trans with (e1 * /2).
        now apply Rmult_le_compat_r; lt0.
      now apply Rmult_le_compat_neg_l; lt0.
    eapply ex_intro;split;[eapply help4, refl_equal; lt0 | ].
    now split;[apply help1 | apply help2]; lt0.
  split; cycle 1.
    apply Rle_trans with (sqrt (sqrt (/ 2)) + e2 * e - v_ 1 (/sqrt 2)).    
      repeat apply Rplus_le_compat_r.
      apply sqrt_le_1; try lt0.
        now interval.
      now assert (e1 * e <= 0) by (apply Rmult_le_0_r; lt0); lt0.
    unfold v_; simpl; rewrite Rmult_1_l. 
    assert (e2 * e <= 0) by (apply Rmult_le_0_r; lt0).
    now rewrite inv_sqrt; lt0.
  replace (- (3 / 2) * (10 * e)) with (-15 * e) by field.
  rewrite (Rplus_comm _ (_ * e)); unfold Rminus; rewrite (Rplus_assoc (_ * e)).
  replace (-15 * e) with (-1 * e + (-14 * e)) by ring.
  apply Rplus_le_compat;[apply Rmult_le_compat_r; try lt0 | ].
  unfold v_; simpl; rewrite Rmult_1_l.
  assert (0 < sqrt (sqrt (/2)) + 2 * e1 * e).
    apply Rlt_le_trans with ( / 2 + 2 * -1 * e).
      now lt0.
    apply Rplus_le_compat;[interval | rewrite !Rmult_assoc].
    now apply Rmult_le_compat_l;[| apply Rmult_le_compat_r]; lt0.
  assert (0 < sqrt (/ 2) + e1 * e).
    apply Rlt_le_trans with ( / 2 + -1 * e).
      now lt0.
    apply Rplus_le_compat;[interval | ].
    now apply Rmult_le_compat_r; lt0. 
  assert (intermediate :sqrt (sqrt (/2)) + 2 * e1 * e <= sqrt (sqrt (/2) + e1 * e)).
    apply pow_incr_inv with 1%nat; auto.
      apply sqrt_lt_R0.
      assumption.
    rewrite pow2_sqrt;[ | lt0].
    replace ((sqrt (sqrt (/2)) + 2 * e1 * e) ^ 2) with
            (sqrt (sqrt (/2)) ^ 2 + e1 * e * (4 * (sqrt(sqrt (/ 2)) + (e1 * e))))
     by ring.
    rewrite pow2_sqrt;[ | lt0].
    apply Rplus_le_compat_l, Rminus_le.
    replace (e1 * e) with (e1 * e * 1) at 3 by ring.
    now rewrite <- Rmult_minus_distr_l; interval.
  assert (h : forall a b c, a + c <= b -> a <= b - c) by (intros; psatzl R).
  apply h, Rle_trans with (2 := intermediate).
  rewrite -> inv_sqrt, Rplus_comm; try lt0.
  now apply Rplus_le_compat_l, Rmult_le_compat_r; lt0.
assert (-1 * (10 * e) <= r_sqrt (/2) - /sqrt 2 <= 0).
  rewrite inv_sqrt; try lt0.
  rewrite Qe1; split. 
    unfold Rminus; rewrite -> (Rplus_comm (sqrt _)), Rplus_assoc.
    rewrite -> Rplus_opp_r, Rplus_0_r, <- Rmult_assoc.
    now apply Rmult_le_compat_r; lt0.
  now assert (e1 * e <= 0) by (apply Rmult_le_0_r; lt0); lt0.
apply t; auto; try (unfold u_, v_, salamin_sumand; simpl; ring); try lt0;
 simpl; rewrite ?Rmult_1_r; try lt0.
Qed.

End rounded_operations.