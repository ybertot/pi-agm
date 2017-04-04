Require Import rounding_correct.

(*TODO rempove this line once rounding_correct is recompiled. *)

Open Scope R_scope.
Section rounded_operations.

Variables (e : R) (r_div : R -> R -> R) (r_sqrt : R -> R)
           (r_mult : R -> R -> R)(r_square : R -> R).

Hypothesis ce : 0 < e < /1000.

Hypothesis r_mult_spec :
  forall x y, 0 <= x -> 0 <= y -> x * y - e < r_mult x y <= x * y.

Hypothesis r_div_spec :
  forall x y, (0 < y) -> x/y - e < r_div x y <= x/y.

Hypothesis r_sqrt_spec :
  forall x, 0 <= x -> sqrt x - e < r_sqrt x <= sqrt x.

Hypothesis r_square_spec :
  forall x, x ^ 2 - e < r_square x <= x ^ 2.

Lemma sumand_error_ub  u v e' h h' k :
0 <= e' <= / 1000 ->
e <= e' ->
-e' <= h <= 0 -> -e' <= h' <= 0 ->
2 * e' <= / 4 * / 2 ^ k ->
0 <= u - v <= /4 * / 2 ^ k ->
2 ^ k * r_square ((u + h) - (v + h')) <= 2 ^ k * (u - v) ^ 2 + 2 / 3 * e'.
Proof.
intros (* intu intv *) inte' ee' inth inth' ek uv.
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
(* TODO : understand why this does not work. 
replace ((3 / 4 + 2 ^ k)  * e') with ((/2 * e' + /4 * e') + 2 ^ k * e') at 2 by field. *)
apply Rle_trans with (/2 * e' + / 6 * e' + 0);[|apply Req_le; field].
rewrite !(Rmult_plus_distr_l (2 ^ k)); apply Rplus_le_compat.
  apply Rplus_le_compat;[rewrite <- Rmult_assoc | ]. 
    destruct (Rle_dec 0 (h - h')).
      apply Rmult_le_compat; try lt0.
        now repeat apply Rmult_le_pos; lt0.
      rewrite <- Rmult_assoc; apply Rmult_le_reg_l with (/(2 ^ k * 2)); try lt0.
      rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
      now apply Rle_trans with (1 := proj2 uv), Req_le; field; lt0.
    apply Rle_trans with (2 ^ k * (2 * (u - v)) * 0).
      apply Rmult_le_compat_l.
        repeat apply Rmult_le_pos; lt0.
      lt0.
    now rewrite Rmult_0_r; lt0.
  destruct (Rle_dec 0 (h - h')).
    replace (2 ^ k * (h - h') ^ 2) with (2 ^ k * (h - h') * (h - h')) by ring.
    apply Rmult_le_compat; try lt0.
      apply Rmult_le_pos; lt0.
    apply Rmult_le_reg_l with (/ 2 ^ k);[lt0 |].
    now rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; lt0.
    replace (2 ^ k * (h - h') ^ 2) with (2 ^ k * (h' - h) * (h' - h)) by ring.
  apply Rmult_le_compat; try lt0.
  apply Rmult_le_reg_l with (/ 2 ^ k);[lt0 |].
  now rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; lt0.
enough (0 <= - (2 ^ k * (e1 * e'))) by psatzl R.
rewrite -> Ropp_mult_distr_r, Ropp_mult_distr_l.
now repeat apply Rmult_le_pos; lt0.
Qed.

Lemma sumand_error_lb  u v e' h h' k :
(*
42/50 <= u <= 43/50 -> 42/50 <= v <= 43/50 -> *)
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
  apply Rplus_le_compat;[rewrite <- Rmult_assoc | ]. 
    destruct (Rle_dec 0 (h - h')).
      apply Rle_trans with 0; try lt0.
      now repeat apply Rmult_le_pos; lt0.
    enough (2 ^ k * (2 * (u - v)) * (h' - h) <= /2 * e') by psatzl R.
    apply Rmult_le_compat; try lt0.
      now apply Rmult_le_pos; lt0.
    rewrite <- Rmult_assoc; apply Rmult_le_reg_l with (/(2 ^ k * 2)); try lt0.
    rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; try lt0.
    now apply Rle_trans with (1 := proj2 uv), Req_le; field; lt0.
  now apply Rle_trans with 0;[| apply Rmult_le_pos;[| apply pow2_ge_0 ]];lt0.
apply Rmult_le_compat_l;[lt0 | apply Rmult_le_compat_r; lt0].
Qed.

Lemma agm1_error e' a b h h':
-e' <= h <= 0 -> -e' <= h' <= 0 ->
  (a + b) / 2 - e' <= ((a + h) + (b + h')) / 2 <= (a + b)/2.
Proof.
split;[ | psatzl R].
replace ((a + h + (b + h')) / 2) with ((a + b) / 2 + (h + h') / 2) by field.
now apply Rplus_le_compat_l; psatzl R.
Qed.

Lemma agm2_error e' u v h h' :
  85355/100000 <= u <= 85356/100000 ->
  84089/100000 <= v <= 84090/100000 ->
  0 <= e' <= /100000 ->
  e <= / 10 * e' ->
  e' <= h <= 0 -> e' <= h' <= 0 ->
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
  now destruct (r_mult_spec (u + h) (v + h')); try psatzl R.
assert (exists e2, r_sqrt ((u + h) * (v + h') + e1 * e') =
                       sqrt ((u + h) * (v + h') + e1 * e') + e2 * e' /\
                   - /10 <= e2 <= 0) as [e2 [Q Pe2]];[| rewrite Q; clear Q].
  destruct (r_sqrt_spec((u + h) - (v + h'))); try psatzl R.
split; cycle 1.
  apply Rle_trans with ((sqrt (u * v + 0)) + e2 * e').
    assert (-/100000 <= h <= 0) by psatzl R.
    assert (-/100000 <= h' <= 0) by psatzl R.
    apply Rplus_le_compat_r, sqrt_le_1;[interval | interval | ].
    replace ((u + h) * (v + h')) with 
        ((u * v) + (u + h) * h' + v * h) by ring.
    now rewrite !Rplus_assoc; apply Rplus_le_compat_l; interval.
  rewrite <- (Rplus_0_r (sqrt (u * v))); apply Rplus_le_compat.
    now rewrite Rplus_0_r; apply Req_le.
  now assert (pn : 0 <= -(e2 * e')) by lt0; psatzl R.
replace (sqrt (u * v) - 3/2 * e') with
   (sqrt (u * v) - 7/5 * e' - /10 * e') by field.
apply Rplus_le_compat;[|rewrite Ropp_mult_distr_l; apply Rmult_le_compat_r;lt0].
assert (sf : ((u + h) * (v + h') + e1 * e' =
          u * v + h' * (u + h) + h * v + e1 * e')) by ring.
assert (cmp : (u + h) * (v + h') + e1 * e' <= u * v).
  replace (u * v) with (u * v + 0) by ring.
  rewrite -> sf, !Rplus_assoc; apply Rplus_le_compat_l.
  assert (0 < u + h) by psatzl R.
  assert (help : forall a, 0 <= -a -> a <= 0) by (intros; psatzl R); apply help.
  now rewrite -> !Ropp_plus_distr, !Ropp_mult_distr_l; lt0.
assert (mnh : Rmin (u * v) ((u + h) * (v + h') + e1 * e') =
                    ((u + h) * (v + h') + e1 * e')).
   now rewrite Rmin_right; lt0.
assert (mxh : Rmax (u * v) ((u + h) * (v + h') + e1 * e') = u * v).
   now rewrite Rmax_left; lt0.
assert ( -/100000 <= h <= 0) by psatzl R.
assert ( -/100000 <= h' <= 0) by psatzl R.
assert ( 0 <= e' <= /100000) by psatzl R.
set (a0 := Rmin (u * v) ((u + h) * (v + h') + e1 * e')).
set (b0 := Rmax (u * v) ((u + h) * (v + h') + e1 * e')).
assert (0 < a0) by (unfold a0; rewrite mnh; interval).
assert (ds' : forall x, a0 <= x <= b0 -> 
           is_derive sqrt x ((fun y => 1 / (2 * sqrt x)) x)).
  intros x intx; auto_derive;[| field]; psatzl R.
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
interval.
Qed.

(* TODO : transfer back to elliptic integral.v *)
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

Lemma sum_error s h h' k e' (k1 : (1 <= k)%nat) :
  0 <= e' <= /10 ^ (k + 3) / 2 ^ k ->
  e <= / 10 * e' ->
  -((3 / 2) ^ (k - 1) * e') <= h <= 0 ->
  -((3 / 2) ^ (k - 1) * e') <= h' <= 0 ->
  Rabs (s - (1 - sum_f_R0 salamin_sumand k)) <= 3 ^ k / 2 * e' ->
  Rabs ((s - 2 ^ k * r_square ((u_ k (/sqrt 2) + h) - (v_ k (/sqrt 2) + h')))
        - (1 - sum_f_R0 salamin_sumand (S k))) <= 3 ^ (S k) / 2 * e'.
Proof.
intros inte' ee' inth inth' cs.
assert (ls : 3 ^ S k / 2 * e' = 3 ^ k / 2 * e' + 3 ^ k * e').
  now rewrite <- Rmult_plus_distr_r, <- tech_pow_Rmult; field.
rewrite -> ls, tech5.
assert (help : forall a b c d, a - b - (1 - (c + d)) = a - (1 - c) + (d - b))
  by (intros; ring).
rewrite help; clear help; apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat; try lt0.
assert (0 <= (3 / 2) ^ (k - 1) * e' <= /1000).
  split;[lt0 | ].
  apply Rmult_le_reg_l with (/(3 / 2) ^ (k - 1));[lt0 | ].
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;
    [apply Rle_trans with (1 := proj2 inte')| lt0].
  unfold Rdiv; rewrite -> (Rmult_comm (/10 ^ (k + 3))).
  apply Rmult_le_compat; try lt0; cycle 1.
    apply Rle_Rinv; try lt0; replace 1000 with (10 ^ 3) by ring; apply Rle_pow.
      now lt0.
    now lia.
  apply Rle_Rinv;[lt0 | lt0 | apply Rle_trans with ((3/2) ^ k)].
    now apply Rle_pow;[lt0 | lia].
  now apply pow_incr; psatzl R.
assert (e <= (3 / 2) ^ (k - 1) * e').
  apply Rle_trans with (1 := ee'); apply Rmult_le_compat_r;[lt0 | ].
  now apply Rle_trans with 1;[| apply pow_R1_Rle]; psatzl R.
assert (0 <= u_ k (/sqrt 2) - v_ k (/sqrt 2) <= /4 * / 2 ^ k).
  split.
    now apply Rlt_le, Rlt_Rminus, v_lt_u, ints.
  assert (s24 : /4 <= /sqrt 2) by interval.
  assert (s21 : /sqrt 2 <= 1) by interval.
  assert (s2m : 1 - /sqrt 2 < 1) by interval.
  assert (t := agm_conv_speed 1 (/sqrt 2) (1 - /sqrt 2) k Rlt_0_1 s24 s21
               (Rle_refl _) s2m).
  apply Rle_trans with (1 := t); clear t.
  apply Rlt_le, ln_lt_inv;[apply pow_lt; interval | lt0 | ].
  rewrite <- Rpower_pow;[|interval].
  unfold Rpower; rewrite ln_exp.
  clear -k1; induction k1.
    now simpl; rewrite Rmult_1_r; interval.
  rewrite -> Nat.pow_succ_r, mult_INR, Rmult_assoc; simpl INR; auto with arith.
  apply Rlt_trans with (2 * ln (/4 * /2 ^ m)).
    apply Rmult_lt_compat_l;[lt0 | assumption ].
  rewrite <- tech_pow_Rmult, (Rinv_mult_distr 2 (2 ^ m));[ | lt0 | lt0].
  replace (2 * ln (/ 4 * / 2 ^ m)) with (ln (/4 * /2 ^ m) + ln (/4 * /2 ^ m))
     by ring.
  rewrite !ln_mult; try lt0; rewrite <- !Rplus_assoc; apply Rplus_lt_compat_r.
  rewrite Rplus_assoc; apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (ln (/2) + ln (/4));[ | interval].
  apply Rplus_le_compat_r; rewrite !ln_Rinv; try lt0.
  apply Ropp_le_contravar, ln_le; try lt0.
  now replace 2 with (2 ^ 1) at 1 by ring; apply Rle_pow; auto; lt0.
assert (2 * ((3 / 2) ^ (k - 1) * e') <= /4 * / 2 ^ k).
  apply Rle_trans with (2 * ((3 / 2) ^ k * (/10 ^ (k + 3) / 2 ^ k))).
    repeat (apply Rmult_le_compat; try lt0).
    now apply Rle_pow; try lia; psatzl R.
  replace (10 ^ (k + 3)) with (1000 * 10 ^ k) by
     (rewrite -> pow_add, Rmult_comm; ring).
  rewrite Rinv_mult_distr; try lt0; unfold Rdiv.
  rewrite !Rinv_pow; try lt0.
  rewrite -> (Rmult_assoc (/_)), <- Rpow_mult_distr, <- (Rmult_assoc _ (/_)).
  rewrite <- (Rmult_comm (/_)), (Rmult_assoc (/_)), <- Rpow_mult_distr.
  rewrite <- Rmult_assoc; apply Rmult_le_compat; try lt0.
  now apply pow_incr; psatzl R.
destruct (Rle_dec 0 (salamin_sumand (S k) -
                 2 ^ k * r_square (u_ k (/sqrt 2) + h - (v_ k (/sqrt 2) + h')))).
  rewrite Rabs_right; [|apply Rle_ge; assumption].
  assert (help : forall a b c, a - c <= b -> a - b <= c) by (intros; psatzl R).
  apply help; clear help.
  apply Rle_trans with (2 ^ k * (u_ k (/ sqrt 2) - v_ k (/ sqrt 2)) ^ 2 -
      (2 / 3 + 2 ^ k) * ((3 / 2) ^ (k - 1) * e')); cycle 1.
    assert (t := sumand_error_lb (u_ k (/sqrt 2)) (v_ k (/sqrt 2))
               ((3/2) ^ (k - 1) * e') h h' k ).
    now apply t; auto; clear t.
  apply Rplus_le_compat;[apply Req_le | ].
    unfold salamin_sumand; simpl (S k =? 0); lazy iota.
    now replace (S k - 1)%nat with k by lia.
  apply Ropp_le_contravar; rewrite <- Rmult_assoc; apply Rmult_le_compat_r;[lt0|].
  replace k with (S (k - 1)) at 1 by lia.
  rewrite <- tech_pow_Rmult, Rmult_plus_distr_r, Rmult_assoc, <- Rpow_mult_distr.
  replace (2 * (3 / 2)) with 3 by field.
  apply Rle_trans with (3 ^ (k - 1) + 2 * 3 ^ (k - 1)).
    apply Rplus_le_compat_r.
    destruct (k - 1)%nat as [ | n'];[simpl; psatzl R | ].
    rewrite <- !tech_pow_Rmult, <- Rmult_assoc; apply Rmult_le_compat; try lt0.
    now apply pow_incr; psatzl R.
  apply Req_le.
  replace (3 ^ (k - 1)) with (1 * 3 ^ (k - 1)) at 1 by ring.
  rewrite <- Rmult_plus_distr_r, tech_pow_Rmult; replace (S (k - 1)) with k by lia.
  replace (3 ^ (k + 1)) with (3 * 3 ^ k);[ field | ].
  now rewrite pow_add; simpl (3 ^ 1); ring.
rewrite Rabs_left;[ |lt0 ].
assert (help : forall a b c, b <= a + c -> -(a - b) <= c) by (intros; psatzl R).
apply help; clear help.
apply Rle_trans  with (2 ^ k * (u_ k (/ sqrt 2) - v_ k (/ sqrt 2)) ^ 2 +
      2 / 3 * ((3 / 2) ^ (k - 1) * e')); cycle 1.
  apply Rplus_le_compat.
    unfold salamin_sumand; simpl (S k =? 0); lazy iota.
    now replace (S k - 1)%nat with k by lia; apply Req_le.
  replace k with (S (k - 1)) at 2 by lia.
  rewrite <- tech_pow_Rmult, <- Rmult_assoc.
  apply Rmult_le_compat_r;[lt0 | apply Rmult_le_compat; try lt0].
  now apply pow_incr; psatzl R.
assert (t := sumand_error_ub (u_ k (/sqrt 2)) (v_ k (/sqrt 2)) ((3/2) ^ (k - 1) * e')
                 h h' k ).
now apply t; auto.
Qed.

Fixpoint rsalamin_rec (n : nat)
   (a b am1 bm1 sum twopk :R) :=
  match n with
    0 => r_div (4 * r_square a) sum
  | S p => (rsalamin_rec p (r_div (a + b) 2) (r_sqrt (r_mult a b)) a b
            (let v := (am1 - bm1) in
            sum - (twopk * r_square v)))%R (2 * twopk)
  end.

Definition rsalamin (n : nat) :=
  let s2 := r_div 1 (r_sqrt 2) in
  let a1 := r_div (1 + s2) 2 in
  let b1 := r_sqrt s2 in
  let twopk := 1 in
  rsalamin_rec n a1 b1 1 s2 1 twopk.

Lemma rsalamin_rec_correct n p a b am1 bm1 sum twopk ha hb ha1 hb1 hsm :
  (1 <= n)%nat ->
  a = u_ n (/sqrt 2) + ha -> b = v_ n (/sqrt 2) + hb ->
  am1 = u_ (n - 1) (/sqrt 2) + ha1 -> bm1 = v_ (n - 1) (/sqrt 2) + hb1 ->
  sum = 1 - sum_f_R0 salamin_sumand (n - 1) + hsm ->
  twopk = 2 ^ (n - 1) ->
  - (3 / 2) ^ n * e <= ha <= 0 ->
  - (3 / 2) ^ n * e <= hb <= 0 ->
  - (3 / 2) ^ (n - 1) * e <= ha1 <= 0 ->
  - (3 / 2) ^ (n - 1) * e <= hb1 <= 0 ->
  Rabs hsm < 3 ^ n / 2 * e ->
  0 <= e <= / 10 ^ (n + p + 4) / 3 ^ (n + p) ->
  Rabs (rsalamin_rec p a b am1 bm1 sum twopk -
        ((4 * u_ n (/sqrt 2) ^ 2) /
        (1 - sum_f_R0 salamin_sumand ((p + n) - 1)))) < 
   8 * 3 ^ (p + n) * e + 10 * e.
Proof.
revert a b am1 bm1 sum twopk ha hb ha1 hb1 hsm.
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
  intros a b am1 bm1 sum twopk ha hb ha1 hb1 hsm n1 aq bq a1q b1q sq tq
   intha inthb inta1 intb1 intsm inte.
  assert (-/100 <= hsm <= /100).
    apply Fcore_Raux.Rabs_le_inv, Rlt_le, Rlt_trans with (1 := intsm).
    apply Rle_lt_trans with (3 ^ n/2 * (/10 ^ (n + 0 + 4) / 3 ^ (n + 0))).
    now apply Rmult_le_compat_l;lt0.
    replace 100 with (Rpower 10 2) by
          (replace 100 with (10 ^ 2) by ring; rewrite <- Rpower_pow; auto; lt0).
    assert (0 < Rpower 10 2) by (unfold Rpower; lt0).
    rewrite Nat.add_0_r; field_simplify; try split; try lt0.
    unfold Rdiv; rewrite !Rmult_1_l; rewrite  <- (Rpower_1 2) at 1; try lt0.
    rewrite <- Rpower_pow; try lt0; unfold Rpower.
    rewrite <- exp_plus, <- !exp_Ropp; apply exp_increasing.
    assert (0 < ln 2) by interval; assert (0 < ln 10) by interval.
    rewrite plus_INR; replace (INR 4) with 4 by (simpl; ring).
    rewrite Rmult_plus_distr_r; enough (0 <= n * ln 10) by lt0.
    now apply Rmult_le_pos; try lt0; apply pos_INR.
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
  rewrite help; apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (3 ^ (0 + n) * e + 10 * e) with (3 ^ n * e + 1 * e + 8 * e + 1 * e) by
    (rewrite Nat.add_0_l; ring).
  apply Rplus_lt_le_compat; cycle 1.
    rewrite -> Rabs_mult, (Rabs_right e);[ | lt0]; apply Rmult_le_compat_r.
      now lt0.
    now rewrite Rabs_left1; psatzl R.
  rewrite -> Rmult_plus_distr_l, Rdiv_plus_distr, help.
  assert (ssub := salamin_sum_ub (n - 1)).
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat; cycle 1.
    assert (/ (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) < 2).
      rewrite <- (Rinv_involutive 2); try lt0; apply Rinv_lt_contravar.
        apply Rmult_lt_0_compat; try lt0.
      now assert (t := salamin_sum_ub (n -1)); lt0.
    replace (8 * e) with (4 * e * 2) by ring.
    rewrite Rabs_left1; cycle 1.
      apply Rmult_le_0_r;[apply Rmult_le_0_l | ]; try lt0.
      now apply Rmult_le_0_r; lt0.
    apply Rle_lt_trans with
        (4 * e * / (1 - sum_f_R0 salamin_sumand (n - 1) + hsm)).
      unfold Rdiv; rewrite !(Ropp_mult_distr_l (4 * (e1 * e))).
      apply Rmult_le_compat_r;[lt0 | ].
        rewrite -> Ropp_mult_distr_r, Ropp_mult_distr_l.
      apply Rmult_le_compat_l;[lt0 | ].
      now rewrite <- (Rmult_1_l e) at 2; apply Rmult_le_compat_r; lt0.
    now apply Rmult_lt_compat_l; lt0.
  replace ((u_ n (/ sqrt 2) + ha) ^ 2) with
          (u_ n (/ sqrt 2) ^ 2 + (2 * u_ n (/ sqrt 2) * ha + ha ^ 2)) by ring.
  rewrite -> Rmult_plus_distr_l, Rdiv_plus_distr.  
  assert (hel2 : forall a b c, a + b - c = b + (a - c)) by (intros; ring).
  rewrite hel2; clear hel2.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  (Rabs (4 * u_ n (/sqrt 2) ^ 2 /
        (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) +
        4 * (2 * u_ n (/sqrt 2) * ha + ha ^ 2) /
        (1 - sum_f_R0 salamin_sumand (n - 1) + hsm) -
        4 * u_ n (/sqrt 2) ^ 2 /
        (1 - sum_f_R0 salamin_sumand (0 + n - 1))) <
      3 ^ n * e + 1 * e).
      Search