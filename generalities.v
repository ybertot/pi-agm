Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral.
Require Import elliptic_integral arcsinh.
Require Import Interval.Interval_tactic.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

(* standard *)
Lemma CVU_derivable :
  forall f f' g g' c d,
   CVU f' g' c d ->
   (forall x, Boule c d x -> Un_cv (fun n => f n x) (g x)) ->
   (forall n x, Boule c d x -> derivable_pt_lim (f n) x (f' n x)) ->
   forall x, Boule c d x -> derivable_pt_lim g x (g' x).
Proof.
intros f f' g g' c d cvu cvp dff' x bx.
set (rho_ :=
       fun n y =>
           match Req_EM_T y x with
              left _ => f' n x
           |right _ => ((f n y - f n x)/ (y - x)) end).
set (rho := fun y =>
               match Req_EM_T y x with
                 left _ => g' x
               | right _ => (g y - g x)/(y - x) end).
assert (ctrho : forall n z, Boule c d z -> continuity_pt (rho_ n) z).
 intros n z bz.
 destruct (Req_EM_T x z) as [xz | xnz].
  rewrite <- xz.
  intros eps' ep'.
  destruct (dff' n x bx eps' ep') as [alp Pa].
  exists (pos alp);split;[apply cond_pos | ].
  intros z'; unfold rho_, D_x, dist, R_met; simpl; intros [[_ xnz'] dxz'].
   destruct (Req_EM_T z' x) as [abs | _].
    case xnz'; symmetry; exact abs.
   destruct (Req_EM_T x x) as [_ | abs];[ | case abs; reflexivity].
  pattern z' at 1; replace z' with (x + (z' - x)) by ring.
  apply Pa;[psatzl R | exact dxz'].
 destruct (Ball_in_inter c c d d z bz bz) as [delta Pd].
 assert (dz :  0 < Rmin delta (Rabs (z - x))).
  apply Rmin_glb_lt;[apply cond_pos | apply Rabs_pos_lt; psatzl R].
 assert (t' : forall y : R,
      R_dist y z < Rmin delta (Rabs (z - x)) ->
      (fun z : R => (f n z - f n x) / (z - x)) y = rho_ n y).
  intros y dyz; unfold rho_; destruct (Req_EM_T y x) as [xy | xny].
   rewrite xy in dyz.
   destruct (Rle_dec  delta (Rabs (z - x))).
    rewrite -> Rmin_left, R_dist_sym in dyz; unfold R_dist in dyz; psatz R.
   rewrite -> Rmin_right, R_dist_sym in dyz; unfold R_dist in dyz; psatzl R.
  reflexivity.
 apply (continuity_pt_ext_loc (fun z => (f n z - f n x)/(z - x))).
 exists (mkposreal _ dz); exact t'.
 reg;[ | psatzl R].
 apply derivable_continuous_pt; eapply exist.
 apply dff'; assumption.
assert (CVU rho_ rho c d ).
 intros eps ep.
 assert (ep8 : 0 < eps/8) by psatzl R.
 destruct (cvu _ ep8) as [N Pn1].
 assert (cauchy1 : forall n p, (N <= n)%nat -> (N <= p)%nat ->
           forall z, Boule c d z -> Rabs (f' n z - f' p z) < eps/4).
  intros n p nN pN z bz; replace (eps/4) with (eps/8 + eps/8) by field.
  rewrite <- Rabs_Ropp.
  replace (-(f' n z - f' p z)) with (g' z - f' n z - (g' z - f' p z)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp.
  apply Rplus_lt_compat; apply Pn1; assumption.
 assert (step_2 : forall n p, (N <= n)%nat -> (N <= p)%nat ->
         forall y, Boule c d y -> x <> y ->
         Rabs ((f n y - f n x)/(y - x) - (f p y - f p x)/(y - x)) < eps/4).
  intros n p nN pN y b_y xny.
  assert (mm0 : (Rmin x y = x /\ Rmax x y = y) \/ 
                (Rmin x y = y /\ Rmax x y = x)).
   destruct (Rle_dec x y).
    rewrite -> Rmin_left, Rmax_right; psatzl R.
   now rewrite -> Rmin_right, Rmax_left; psatzl R.
  assert (mm : Rmin x y < Rmax x y).
   destruct mm0 as [[q1 q2] | [q1 q2]]; generalize (Rmin_Rmax x y).
   now rewrite -> q1, q2; intros; psatzl R.
   now psatzl R.
  assert (dm : forall z, Rmin x y <= z <= Rmax x y ->
            derivable_pt_lim (fun x => f n x - f p x) z (f' n z - f' p z)).
   intros z intz; rewrite <- is_derive_Reals; apply: is_derive_minus.
    rewrite is_derive_Reals.
    apply dff'; apply Boule_convex with (Rmin x y) (Rmax x y);
      destruct mm0 as [[q1 q2] | [q1 q2]]; revert intz; rewrite -> ?q1, ?q2; intros;
     try assumption.
   rewrite is_derive_Reals.
   apply dff'; apply Boule_convex with (Rmin x y) (Rmax x y);
      destruct mm0 as [[q1 q2] | [q1 q2]]; revert intz; rewrite -> ?q1, ?q2;
    intros;
     try assumption.

  replace ((f n y - f n x) / (y - x) - (f p y - f p x) / (y - x))
    with (((f n y - f p y) - (f n x - f p x))/(y - x)) by (field; psatzl R).
  destruct (MVT_cor2 (fun x => f n x - f p x) (fun x => f' n x - f' p x)
             (Rmin x y) (Rmax x y) mm dm) as [z [Pz inz]].
  destruct mm0 as [[q1 q2] | [q1 q2]].
   replace ((f n y - f p y - (f n x - f p x))/(y - x)) with
    ((f n (Rmax x y) - f p (Rmax x y) - (f  n (Rmin x y) - f p (Rmin x y)))/
      (Rmax x y - Rmin x y)) by (rewrite -> q1, q2; reflexivity).
   unfold Rdiv; rewrite -> Pz, Rmult_assoc, Rinv_r, Rmult_1_r.
    apply cauchy1; auto.
    apply Boule_convex with (Rmin x y) (Rmax x y);
      revert inz; rewrite -> ?q1, ?q2; intros;
     assumption || psatzl R.
   rewrite -> q1, q2; psatzl R.
  replace ((f n y - f p y - (f n x - f p x))/(y - x)) with
    ((f n (Rmax x y) - f p (Rmax x y) - (f  n (Rmin x y) - f p (Rmin x y)))/
      (Rmax x y - Rmin x y)).
   unfold Rdiv; rewrite -> Pz, Rmult_assoc, Rinv_r, Rmult_1_r.
    apply cauchy1; auto.
    apply Boule_convex with (Rmin x y) (Rmax x y);
     revert inz; rewrite -> ?q1, ?q2; intros;
    assumption || psatzl R.
   rewrite -> q1, q2; psatzl R.
  rewrite -> q1, q2; field; psatzl R.
 assert (unif_ac :
  forall n p, (N <= n)%nat -> (N <= p)%nat ->
     forall y, Boule c d y ->
       Rabs (rho_ n y - rho_ p y) <= eps/2).
  intros n p nN pN y b_y.
  destruct (Req_dec x y) as [xy | xny].
   destruct (Ball_in_inter c c d d x bx bx) as [delta Pdelta].
   destruct (ctrho n y b_y _ ep8) as [d' [dp Pd]].
   destruct (ctrho p y b_y _ ep8) as [d2 [dp2 Pd2]].
   assert (0 < (Rmin (Rmin d' d2) delta)/2) by lt0.
   apply Rle_trans with (1 := R_dist_tri _ _ (rho_ n (y + Rmin (Rmin d' d2) delta/2))).
   replace (eps/2) with (eps/8 + (eps/4 + eps/8)) by field.
   apply Rplus_le_compat.
    rewrite R_dist_sym; apply Rlt_le, Pd;split;[split;[exact I | psatzl R] | ].
    simpl; unfold R_dist.
    unfold Rminus; rewrite -> (Rplus_comm y), Rplus_assoc, Rplus_opp_r, Rplus_0_r.
    rewrite Rabs_pos_eq;[ | psatzl R].      
    apply Rlt_le_trans with (Rmin (Rmin d' d2) delta);[psatzl R | ].
    apply Rle_trans with (Rmin d' d2); apply Rmin_l.
   apply Rle_trans with (1 := R_dist_tri _ _ (rho_ p (y + Rmin (Rmin d' d2) delta/2))).
   apply Rplus_le_compat.
    apply Rlt_le.
     replace (rho_ n (y + Rmin (Rmin d' d2) delta / 2)) with
          ((f n (y + Rmin (Rmin d' d2) delta / 2) - f n x)/
            ((y + Rmin (Rmin d' d2) delta / 2) - x)).
     replace (rho_ p (y + Rmin (Rmin d' d2) delta / 2)) with
          ((f p (y + Rmin (Rmin d' d2) delta / 2) - f p x)/
             ((y + Rmin (Rmin d' d2) delta / 2) - x)).
      apply step_2; auto; try psatzl R.
      assert (0 < pos delta) by (apply cond_pos).
      apply Boule_convex with y (y + delta/2).
        assumption.
       destruct (Pdelta (y + delta/2)); auto.
       rewrite xy; unfold Boule; rewrite Rabs_pos_eq; try psatzl R; auto.
      split; try psatzl R.
      apply Rplus_le_compat_l, Rmult_le_compat_r;[lt0 | apply Rmin_r].
     unfold rho_.
     destruct (Req_EM_T (y + Rmin (Rmin d' d2) delta/2) x);psatzl R.
    unfold rho_.
    destruct (Req_EM_T (y + Rmin (Rmin d' d2) delta / 2) x); psatzl R.
   apply Rlt_le, Pd2; split;[split;[exact I | psatzl R] | ].
   simpl; unfold R_dist.
   unfold Rminus; rewrite -> (Rplus_comm y), Rplus_assoc, Rplus_opp_r, Rplus_0_r.
   rewrite Rabs_pos_eq;[ | psatzl R].      
   apply Rlt_le_trans with (Rmin (Rmin d' d2) delta); [psatzl R |].
   apply Rle_trans with (Rmin d' d2).
    solve[apply Rmin_l].
   solve[apply Rmin_r].
  apply Rlt_le, Rlt_le_trans with (eps/4);[ | psatzl R].
  unfold rho_; destruct (Req_EM_T y x); solve[auto].
 assert (unif_ac' : forall p, (N <= p)%nat ->
           forall y, Boule c d y -> Rabs (rho y - rho_ p y) < eps).
  assert (cvrho : forall y, Boule c d y -> Un_cv (fun n => rho_ n y) (rho y)).
   intros y b_y; unfold rho_, rho; destruct (Req_EM_T y x).
    intros eps' ep'; destruct (cvu eps' ep') as [N2 Pn2].
    exists N2; intros n nN2; rewrite R_dist_sym; apply Pn2; assumption.
   apply CV_mult.
    apply CV_minus.
     apply cvp; assumption.
    apply cvp; assumption.
   intros eps' ep'; simpl; exists 0%nat; intros; rewrite R_dist_eq; assumption.
  intros p pN y b_y.
  replace eps with (eps/2 + eps/2) by field.
  assert (ep2 : 0 < eps/2) by psatzl R.
  destruct (cvrho y b_y _ ep2) as [N2 Pn2].
  apply Rle_lt_trans with (1 := R_dist_tri _ _ (rho_ (max N N2) y)).
  apply Rplus_lt_le_compat.
   solve[rewrite R_dist_sym; apply Pn2, Max.le_max_r].
  apply unif_ac; auto; solve [apply Max.le_max_l].
 exists N; intros; apply unif_ac'; solve[auto].
intros eps ep.
destruct (CVU_continuity _ _ _ _ H ctrho x bx eps ep) as [delta [dp Pd]].
exists (mkposreal _ dp); intros h hn0 dh.
replace ((g (x + h) - g x) / h) with (rho (x + h)).
 replace (g' x) with (rho x).
  apply Pd; unfold D_x, no_cond;split;[split;[auto | psatzl R] | ].
  simpl; unfold R_dist; replace (x + h - x) with h by ring; exact dh.
 unfold rho; destruct (Req_EM_T x x) as [ _ | abs];[ | case abs]; reflexivity.
unfold rho; destruct (Req_EM_T (x + h) x) as [abs | _];[psatzl R | ].
replace (x + h - x) with h by ring; reflexivity.
Qed.

Lemma ball_Rabs x y e : ball x e y <-> Rabs (y - x) < e.
Proof. intros; tauto. Qed.

Lemma cv_div2 a : is_lim_seq (fun n => a / 2 ^ n) 0.
Proof.
apply is_lim_seq_mult with a 0.
    now apply is_lim_seq_const.
  apply (is_lim_seq_ext (fun n => (/2) ^ n)).
    now symmetry; apply Rinv_pow; lt0.
apply is_lim_seq_geom; rewrite Rabs_right; lt0.
now unfold is_Rbar_mult; simpl; rewrite Rmult_0_r.
Qed.


Lemma filterlim_sqrt_0 : filterlim sqrt (at_right 0) (at_right 0).
Proof.
intros P [eps peps].
assert (ep2 : 0 < eps * eps) by (destruct eps; simpl; lt0).
exists (mkposreal _ ep2); intros y bay y0.
assert (0 < sqrt y) by lt0; apply peps; auto.
change (Rabs (sqrt y - 0) < eps); rewrite -> Rabs_right, Rminus_0_r; try lt0.
replace (pos eps) with (sqrt (eps * eps)); [ |  now rewrite sqrt_square; lt0].
apply sqrt_lt_1_alt; split;[lt0 | ].
change (Rabs (y - 0) < eps * eps) in bay; revert bay.
now rewrite -> Rabs_right, Rminus_0_r; lt0.
Qed.

Lemma int_arcsinh x :
  0 < x -> RInt (fun y => / sqrt (y ^ 2 + x ^ 2)) 0 (sqrt x) =
           arcsinh (/ sqrt x).
Proof.
intros x0; apply is_RInt_unique.
assert (s0 : 0 < sqrt x) by lt0.
assert (heq  : forall y,  /sqrt (y ^ 2 + x ^ 2) =
                   / x * /sqrt ((y / x) ^ 2 + 1)).
intros y; replace (y ^ 2 + x ^ 2) with (x ^ 2 * ((y / x) ^ 2 + 1))
   by (field; lt0).
  now rewrite -> sqrt_mult, sqrt_pow2; try lt0; field; split; lt0.
apply (is_RInt_ext (fun y => / x * / sqrt ((y / x) ^ 2 + 1))).
  now intros; rewrite heq.
evar_last.
  apply: (is_RInt_comp (fun t => / sqrt (t ^ 2 + 1)) (fun y => y / x)
          (fun _ => / x)).
    now intros; apply: ex_derive_continuous; auto_derive; repeat split; lt0.
  now intros z _; split;[auto_derive; lt0 | apply continuous_const].
lazy beta; replace (sqrt x / x) with (/ sqrt x); cycle 1.
  now rewrite <- (sqrt_sqrt x) at 3; try lt0; field; lt0.
replace (0 / x) with 0 by (unfold Rdiv; ring).
rewrite <- (Rminus_0_r (arcsinh _)); rewrite <- arcsinh_0 at 2.
apply is_RInt_unique, is_RInt_derive. 
  now intros z intz; rewrite is_derive_Reals; apply derivable_pt_lim_arcsinh.
now intros; apply: ex_derive_continuous; auto_derive; repeat split; lt0.
Qed.


