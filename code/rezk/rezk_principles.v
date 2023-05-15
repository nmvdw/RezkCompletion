(**
 In this file, we derive numerous alternative induction
 and recursion principles for the Rezk completion.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import prelude.basics.
Require Import prelude.cubical_methods.
Require Import rezk.rezk.

Local Open Scope cat.

Section rezk_rec.
  Variable (C : category)
          (Y : UU)
          (rclY : C → Y)
          (rcleqY : ∏ {x₁ x₂ : C},
              z_iso x₁ x₂ → rclY x₁ = rclY x₂)
          (reY : ∏ (x : C), rcleqY (identity_z_iso x) = idpath _)
          (rconcatY : ∏ (x₁ x₂ x₃ : C) (f₁ : z_iso x₁ x₂) (f₂ : z_iso x₂ x₃),
              rcleqY (z_iso_comp f₁ f₂) = rcleqY f₁ @ rcleqY f₂)
          (truncY : isofhlevel 3 Y).

  Definition rezk_rec : rezk C → Y.
  Proof.
    simple refine (rezk_ind
                     (λ _, Y)
                     rclY
                     (λ x₁ x₂ f, PathOverConstant_map1 _ (rcleqY f))
                     (λ x, const_globe_over
                                 (re C x)
                                 (rcleqY (identity_z_iso x))
                                 (idpath _)
                                 (reY x))
                     _
                     (λ _, truncY)) ; simpl.
    intros x₁ x₂ x₃ f₁ f₂.
    simple refine (globe_over_whisker
                     (λ _, Y)
                     _
                     (idpath _)
                     (PathOver_inConstantFamily_concat _ _)
                     (const_globe_over
                        (rconcat C f₁ f₂)
                        (rcleqY (z_iso_comp f₁ f₂))
                        (rcleqY f₁ @ rcleqY f₂)
                        (rconcatY x₁ x₂ x₃ f₁ f₂)
                     )
                  ).
  Defined.

  Definition rezk_rec_beta_rcleq (x₁ x₂ : C) (f : z_iso x₁ x₂)
    : maponpaths rezk_rec (rcleq C f) = rcleqY f.
  Proof.
    apply (PathOver_inConstantFamily_inj (rcleq C f)).
    refine (!(apd_const _ _) @ _).
    apply rezk_ind_beta_rcleq.
  Qed.
End rezk_rec.

Arguments rezk_rec {C} Y rclY rcleqY reY rconcatY {truncY}.

(** If the we have a family of sets, then we can simplify the induction principle. *)
Section rezk_ind_set.
  Variable (C : category)
          (Y : rezk C → UU)
          (rclY : ∏ (x : C), Y(rcl C x))
          (rcleqY : ∏ (x₁ x₂ : C) (f : z_iso x₁ x₂),
              PathOver (rcleq C f) (rclY x₁) (rclY x₂))
          (truncY : ∏ (x : rezk C), isaset (Y x)).

  Definition rezk_ind_set : ∏ (x : rezk C), Y x.
  Proof.
    simple refine (rezk_ind Y rclY rcleqY _ _ _)
    ; intros.
    - apply path_globe_over_hset.
      apply truncY.
    - apply path_globe_over_hset.
      apply truncY.
    - apply hlevelntosn.
      apply truncY.
  Defined.

  Definition rezk_ind_set_beta_rcl (x : C)
    : rezk_ind_set (rcl C x) = rclY x
    := idpath _.

  Definition rezk_ind_set_beta_rcleq : ∏ (x₁ x₂ : C) (f : z_iso x₁ x₂),
      apd rezk_ind_set (rcleq C f)
      =
      rcleqY x₁ x₂ f.
  Proof.
    apply rezk_ind_beta_rcleq.
  Qed.
End rezk_ind_set.

Arguments rezk_ind_set {C} Y rclY rcleqY truncY.

(** If the we have a family of propositions, then we can simplify the induction principle. *)
Section rezk_ind_prop.
  Variable (C : category)
          (Y : rezk C → UU)
          (rclY : ∏ (x : C), Y(rcl C x))
          (truncY : ∏ (x : rezk C), isaprop (Y x)).

  Definition rezk_ind_prop : ∏ (x : rezk C), Y x.
  Proof.
    simple refine (rezk_ind_set Y rclY _ _).
    - intros.
      apply PathOver_path_hprop.
      apply truncY.
    - intro.
      apply hlevelntosn.
      apply truncY.
  Qed.
End rezk_ind_prop.

Arguments rezk_ind_prop {C} Y rclY.

(** The double recursion principle.
    We use [gquot_rec], [gquot_ind_set] and [gquot_ind_prop] to define it.
 *)
Section rezk_double_rec.
  Variable (C₁ C₂ : category)
          (Y : UU)
          (truncY : isofhlevel 3 Y).

  Variable (f : C₁ → C₂ → Y)
          (fr : ∏ (x : C₁) (y₁ y₂ : C₂),
              z_iso y₁ y₂ -> f x y₁ = f x y₂)
          (fre : ∏ (x : C₁) (y : C₂),
              fr x y y (identity_z_iso y) = idpath _)
          (frc : ∏ (x : C₁) (y₁ y₂ y₃ : C₂)
                  (f₁ : z_iso y₁ y₂) (f₂ : z_iso y₂ y₃),
              fr x y₁ y₃ (z_iso_comp f₁ f₂)
              =
              (fr x y₁ y₂ f₁) @ (fr x y₂ y₃ f₂))
          (fl : ∏ (x₁ x₂ : C₁) (y : C₂),
               z_iso x₁ x₂ -> f x₁ y = f x₂ y)
          (fle : ∏ (x : C₁) (y : C₂),
               fl x x y (identity_z_iso x) = idpath _)
          (flc : ∏ (x₁ x₂ x₃ : C₁) (y : C₂)
                  (f₁ : z_iso x₁ x₂) (f₂ : z_iso x₂ x₃),
               fl x₁ x₃ y (z_iso_comp f₁ f₂)
               =
               (fl x₁ x₂ y f₁) @ (fl x₂ x₃ y f₂))
          (fp : ∏ (x₁ x₂ : C₁) (y₁ y₂ : C₂)
                 (f₁ : z_iso x₁ x₂) (f₂ : z_iso y₁ y₂),
               square (fl x₁ x₂ y₂ f₁)
                     (fr x₁ y₁ y₂ f₂)
                     (fr x₂ y₁ y₂ f₂)
                     (fl x₁ x₂ y₁ f₁)).

  Definition rezk_double_rec' : rezk C₁ → rezk C₂ → Y.
  Proof.
    intros x y.
    simple refine (rezk_rec _ _ _ _ _ x).
    - refine (λ a, rezk_rec Y (f a) (fr a) (fre a) (frc a) y).
      exact truncY.
    - intros a₁ a₂ g₁ ; simpl.
      simple refine (rezk_ind_set (λ z, _) _ _ _ y).
      + exact (λ b, fl a₁ a₂ b g₁).
      + intros b₁ b₂ g₂.
        apply map_PathOver.
        refine (whisker_square (idpath _) _ _ (idpath _) _).
        * symmetry.
          apply rezk_rec_beta_rcleq.
        * symmetry.
          apply rezk_rec_beta_rcleq.
        * exact (fp a₁ a₂ b₁ b₂ g₁ g₂).
      + intro.
        exact (truncY _ _).
    - abstract
        (intros a ;
         simple refine (rezk_ind_prop (λ z, _) _ _ y) ;
         [ exact (λ b, fle a b)
         | exact (λ _, truncY _ _ _ _)]).
    - abstract
        (intros a₁ a₂ a₃ g ;
         simple refine (rezk_ind_prop (λ z, _) _ _ y) ;
         [ exact (λ b, flc a₁ a₂ a₃ b g)
         | intro ;
           use impred ; intro ;
           exact (truncY _ _ _ _)]).
    - exact truncY.
  Defined.

  Definition rezk_double_rec'_beta_l_rcleq
            {x₁ x₂ : C₁} (y : C₂)
            (g : z_iso x₁ x₂)
    : maponpaths (λ z, rezk_double_rec' z (rcl C₂ y)) (rcleq C₁ g)
      =
      fl x₁ x₂ y g.
  Proof.
    apply rezk_rec_beta_rcleq.
  Qed.

  Definition rezk_double_rec'_beta_r_rcleq
            (x : C₁) {y₁ y₂ : C₂}
            (g : z_iso y₁ y₂)
    : maponpaths (rezk_double_rec' (rcl C₁ x)) (rcleq C₂ g)
      =
      fr x y₁ y₂ g.
  Proof.
    apply (rezk_rec_beta_rcleq C₂).
  Qed.

  Definition rezk_double_rec : rezk C₁ × rezk C₂ → Y
    := uncurry rezk_double_rec'.

  Definition rezk_double_rec_point (x : C₁) (y : C₂)
    : rezk_double_rec (rcl C₁ x ,, rcl C₂ y) = f x y
    := idpath _.

  Definition rezk_double_rec_beta_rcleq
            {x₁ x₂ : C₁} {y₁ y₂ : C₂}
            (g₁ : z_iso x₁ x₂) (g₂ : z_iso y₁ y₂)
    : maponpaths rezk_double_rec (pathsdirprod (rcleq C₁ g₁) (rcleq C₂ g₂))
      =
      fl x₁ x₂ y₁ g₁ @ fr x₂ y₁ y₂ g₂.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (maponpaths (λ z, z @ _) (rezk_rec_beta_rcleq C₁ _ _ _ _ _ _ _ _ _) @ _).
    exact (maponpaths (λ z, _ @ z) (rezk_rec_beta_rcleq C₂ _ _ _ _ _ _ _ _ _)).
  Qed.

  Definition rezk_double_rec_beta_l_rcleq
            {x₁ x₂ : C₁} (y : C₂)
            (g : z_iso x₁ x₂)
    : maponpaths rezk_double_rec (pathsdirprod (rcleq C₁ g) (idpath (rcl C₂ y)))
      =
      fl x₁ x₂ y g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (maponpaths (λ z, z @ _) (rezk_rec_beta_rcleq C₁ _ _ _ _ _ _ _ _ _) @ _).
    apply pathscomp0rid.
  Qed.
  
  Definition rezk_double_rec_beta_r_rcleq
            (x : C₁) {y₁ y₂ : C₂}
            (g : z_iso y₁ y₂)
    : maponpaths rezk_double_rec (pathsdirprod (idpath (rcl C₁ x)) (rcleq C₂ g))
      =
      fr x y₁ y₂ g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    exact (maponpaths (λ z, _ @ z) (rezk_rec_beta_rcleq C₂ _ _ _ _ _ _ _ _ _)).
  Qed.
End rezk_double_rec.

Arguments rezk_double_rec {C₁ C₂} Y {_ _}.
Arguments rezk_double_rec' {C₁ C₂} Y {_ _}.
Arguments rezk_double_rec_beta_rcleq {C₁ C₂} Y {_ _}.

(** Double induction over a family of sets.
    We use the same trick as for double recursion.
 *)
Section rezk_double_ind_set.
  Variable (C₁ C₂ : category)
          (Y : rezk C₁ → rezk C₂ → UU)
          (Yisaset : ∏ (x : rezk C₁) (y : rezk C₂), isaset (Y x y)).
  
  Variable (f : ∏ (x : C₁) (y : C₂), Y (rcl C₁ x) (rcl C₂ y))
          (fr : ∏ (x : C₁) (y₁ y₂ : C₂) (g : z_iso y₁ y₂),
              PathOver (rcleq C₂ g) (f x y₁) (f x y₂))
          (fl : ∏ (x₁ x₂ : C₁) (y : C₂) (g : z_iso x₁ x₂),
              @PathOver
                _ _ _
                (rcleq C₁ g)
                (λ z : rezk C₁, Y z (rcl C₂ y))
                (f x₁ y)
                (f x₂ y)).

  Definition rezk_double_ind_set : ∏ (x : rezk C₁) (y : rezk C₂), Y x y.
  Proof.
    intros x y.
    revert x.
    use rezk_ind_set.
    - intro x.
      revert y.
      use rezk_ind_set.
      + exact (f x).
      + exact (fr x).
      + intro ; apply Yisaset.
    - abstract
        (intros a₁ a₂ g ;
         revert y ;
         use rezk_ind_prop ;
         [ exact (λ b, fl a₁ a₂ b g)
         | intro ;
           apply PathOver_hprop ;
           intro ;
           apply Yisaset]).
    - intro x.
      apply Yisaset.
  Defined.
End rezk_double_ind_set.

Arguments rezk_double_ind_set {C₁ C₂} Y {_ _}.

(** Double induction over a family of propositions.
    We use the same trick as before.
 *)
Section rezk_double_ind_prop.
  Variable (C₁ C₂ : category)
          (Y : rezk C₁ → rezk C₂ → UU)
          (Yisaprop : ∏ (x : rezk C₁) (y : rezk C₂), isaprop (Y x y)).
  
  Variable (f : ∏ (x : C₁) (y : C₂), Y (rcl C₁ x) (rcl C₂ y)).
  
  Definition rezk_double_ind_prop : ∏ (x : rezk C₁) (y : rezk C₂), Y x y.
  Proof.
    intros x y.
    simple refine (rezk_ind_prop (λ z, _) _ _ x).
    + simple refine (λ a, rezk_ind_prop (λ z, _) (f a) _ y).
      intro ; simpl.
      apply Yisaprop.
    + intro ; simpl.
      apply Yisaprop.
  Defined.
End rezk_double_ind_prop.

Arguments rezk_double_ind_prop {C₁ C₂} Y.

Section rezk_triple_ind_set.
  Variable (C₁ C₂ C₃ : category)
          (Y : rezk C₁ → rezk C₂ → rezk C₃ → UU)
          (Yisaset : ∏ (x : rezk C₁) (y : rezk C₂) (z : rezk C₃), isaset (Y x y z)).
  
  Variable (f : ∏ (x : C₁) (y : C₂) (z : C₃), Y (rcl C₁ x) (rcl C₂ y) (rcl C₃ z))
          (fx : ∏ (x₁ x₂ : C₁) (y : C₂) (z : C₃) (g : z_iso x₁ x₂),
              @PathOver
                _ _ _
                (rcleq C₁ g)
                (λ q : rezk C₁, Y q (rcl C₂ y) (rcl C₃ z))
                (f x₁ y z)
                (f x₂ y z))
          (fy : ∏ (x : C₁) (y₁ y₂ : C₂) (z : C₃) (g : z_iso y₁ y₂),
              @PathOver
                _ _ _
                (rcleq C₂ g)
                (λ q : rezk C₂, Y (rcl C₁ x) q (rcl C₃ z))
                (f x y₁ z)
                (f x y₂ z))
          (fz : ∏ (x : C₁) (y : C₂) (z₁ z₂ : C₃) (g : z_iso z₁ z₂),
              PathOver (rcleq C₃ g) (f x y z₁) (f x y z₂)).

  Definition rezk_triple_ind_set : ∏ (x : rezk C₁) (y : rezk C₂) (z : rezk C₃), Y x y z.
  Proof.
    intros x y z.
    revert x.
    use rezk_ind_set.
    - intro x.
      revert y.
      use rezk_ind_set.
      + intro y.
        revert z.
        use rezk_ind_set.
        * exact (λ z, f x y z).
        * apply fz.
        * intro ; apply Yisaset.
      + abstract
          (intros y₁ y₂ g ;
           revert z ;
           use rezk_ind_prop ;
           [ exact (λ z, fy x y₁ y₂ z g)
           | intro ;
             apply PathOver_hprop ;
             intro ;
             apply Yisaset]).
      + intro y.
        apply Yisaset.
    - abstract
        (intros x₁ x₂ g ;
         cbn ;
         revert y z ;
         use rezk_double_ind_prop;
         [ intros ;
           apply PathOver_hprop ;
           intro ;
        apply Yisaset
        | intros ;
          apply fx]).
    - intros.
      apply Yisaset.
  Defined.
End rezk_triple_ind_set.

Arguments rezk_triple_ind_set {C₁ C₂ C₃} Y {_ _ _}.

(** A special instance of double recursion for defining set-relations.
    This requires univalence, because we need to give equalities in [hSet].
    These equalities are made with [path_hset] and two functions need to be given.
    For the higher coherencies, these functions need to satisfy some laws.
 *)
Section rezk_relation.
  Variable (C₁ C₂ : category)
          (R : C₁ → C₂ → hSet)
          (fl : ∏ (x₁ x₂ : C₁) (y : C₂), z_iso x₁ x₂ → R x₁ y → R x₂ y)
          (fr : ∏ (x : C₁) (y₁ y₂ : C₂), z_iso y₁ y₂ → R x y₁ → R x y₂).
  Variable (fl_isweq : ∏ (x₁ x₂ : C₁) (y : C₂) (g : z_iso x₁ x₂), isweq (fl x₁ x₂ y g))
          (fr_isweq : ∏ (x : C₁) (y₁ y₂ : C₂) (g : z_iso y₁ y₂), isweq (fr x y₁ y₂ g)).

  Variable (fl_id : ∏ (x : C₁) (y : C₂), homot (fl x x y (identity_z_iso x)) (λ z, z))
          (fl_comp : ∏ (x₁ x₂ x₃ : C₁) (y : C₂)
                      (g₁ : z_iso x₁ x₂) (g₂ : z_iso x₂ x₃),
                    homot
                      (fl x₁ x₃ y (z_iso_comp g₁ g₂))
                      (fl x₂ x₃ y g₂ ∘ (fl x₁ x₂ y g₁))%functions)
          (fr_id : ∏ (x : C₁) (y : C₂), homot (fr x y y (identity_z_iso y)) (λ z, z))
          (fr_comp : ∏ (x : C₁) (y₁ y₂ y₃ : C₂)
                      (g₁ : z_iso y₁ y₂) (g₂ : z_iso y₂ y₃),
                    homot
                      (fr x y₁ y₃ (z_iso_comp g₁ g₂))
                      (fr x y₂ y₃ g₂ ∘ (fr x y₁ y₂ g₁))%functions)
          (fc : ∏ (x₁ x₂ : C₁) (y₁ y₂ : C₂)
                  (g₁ : z_iso x₁ x₂) (g₂ : z_iso y₁ y₂),
                (homot
                   (fl x₁ x₂ y₂ g₁ ∘ fr x₁ y₁ y₂ g₂)
                   (fr x₂ y₁ y₂ g₂ ∘ fl x₁ x₂ y₁ g₁))%functions
          ).

  Definition fl_weq
    : ∏ (x₁ x₂ : C₁) (y : C₂), z_iso x₁ x₂ → R x₁ y ≃ R x₂ y.
  Proof.
    intros a₁ a₂ b g.
    use make_weq.
    - exact (fl a₁ a₂ b g).
    - exact (fl_isweq a₁ a₂ b g).
  Defined.

  Definition fr_weq
    : ∏ (x : C₁) (y₁ y₂ : C₂), z_iso y₁ y₂ → R x y₁ ≃ R x y₂.
  Proof.
    intros a b₁ b₂ g.
    use make_weq.
    - exact (fr a b₁ b₂ g).
    - exact (fr_isweq a b₁ b₂ g).
  Defined.

  Definition path_hset_fl_refl
            (x : C₁) (y : C₂)
    : @path_HLevel 2 _ _ (fl_weq x x y (identity_z_iso x)) = idpath _.
  Proof.
    rewrite <- path_HLevel_id.
    apply path_HLevel_eq.
    apply fl_id.
  Qed.

  Definition path_hset_fl_trans
            (x₁ x₂ x₃ : C₁) (y : C₂)
            (g₁ : z_iso x₂ x₃) (g₂ : z_iso x₁ x₂)
    : @path_HLevel 2 _ _ (fl_weq x₁ x₃ y (z_iso_comp g₂ g₁))
      =
      (@path_HLevel 2 _ _ (fl_weq x₁ x₂ y g₂))
        @
        @path_HLevel 2 _ _ (fl_weq x₂ x₃ y g₁).
  Proof.
    rewrite <- path_HLevel_comp.
    apply path_HLevel_eq.
    apply fl_comp.
  Qed.
  
  Definition path_hset_fr_refl
            (x : C₁) (y : C₂)
    : @path_HLevel 2 _ _ (fr_weq x y y (identity_z_iso y)) = idpath _.
  Proof.
    rewrite <- path_HLevel_id.
    apply path_HLevel_eq.
    apply fr_id.
  Qed.

  Definition path_hset_fr_trans
            (x : C₁) (y₁ y₂ y₃ : C₂)
            (g₁ : z_iso y₂ y₃) (g₂ : z_iso y₁ y₂)
    : @path_HLevel 2 _ _ (fr_weq x y₁ y₃ (z_iso_comp g₂ g₁))
      =
      (@path_HLevel 2 _ _ (fr_weq x y₁ y₂ g₂))
        @
        @path_HLevel 2 _ _ (fr_weq x y₂ y₃ g₁).
  Proof.
    rewrite <- path_HLevel_comp.
    apply path_HLevel_eq.
    apply fr_comp.
  Qed.

  Definition path_hset_fl_fr
            (x₁ x₂ : C₁) (y₁ y₂ : C₂)
            (g₁ : z_iso x₁ x₂)
            (g₂ : z_iso y₁ y₂)
    : (@path_HLevel 2 _ _ (fr_weq x₁ y₁ y₂ g₂))
        @
        @path_HLevel 2 _ _ (fl_weq x₁ x₂ y₂ g₁)
      =
      (@path_HLevel 2 _ _ (fl_weq x₁ x₂ y₁ g₁))
        @
        @path_HLevel 2 _ _ (fr_weq x₂ y₁ y₂ g₂).
  Proof.
    refine (!(path_HLevel_comp _ _) @ _ @ path_HLevel_comp _ _).
    apply path_HLevel_eq ; cbn.
    apply fc.
  Qed.

  Definition rezk_relation : rezk C₁ → rezk C₂ → hSet.
  Proof.
    simple refine (rezk_double_rec' _ _ _ _ _ _ _ _).
    - apply isofhlevel_HLevel.
    - exact R.
    - exact (λ a b₁ b₂ g, @path_HLevel 2 _ _ (fr_weq a b₁ b₂ g)).
    - exact path_hset_fr_refl.
    - intros.
      apply path_hset_fr_trans.
    - exact (λ a₁ a₂ b g, @ path_HLevel 2 _ _ (fl_weq a₁ a₂ b g)).
    - exact path_hset_fl_refl.
    - intros.
      apply path_hset_fl_trans.
    - intros a₁ a₂ b₁ b₂ g₁ g₂.
      apply path_hset_fl_fr.
  Defined.

  Definition rezk_relation_rcl_rcl (x : C₁) (y : C₂)
    : rezk_relation (rcl C₁ x) (rcl C₂ y) = R x y
    := idpath _.

  Definition rezk_relation_beta_l_rcleq
            {x₁ x₂ : C₁} (y : C₂) (g : z_iso x₁ x₂)
    : maponpaths (λ z, rezk_relation z (rcl C₂ y)) (rcleq C₁ g)
      =
      @path_HLevel 2 _ _ (fl_weq x₁ x₂ y g).
  Proof.
    exact (rezk_double_rec'_beta_l_rcleq C₁ C₂ hSet _ R _ _ _ _ _ _ _ y g).
  Qed.

  Definition rezk_relation_beta_r_rcleq
            (x : C₁) {y₁ y₂ : C₂} (g : z_iso y₁ y₂)
    : maponpaths (rezk_relation (rcl C₁ x)) (rcleq C₂ g)
      =
      @path_HLevel 2 _ _ (fr_weq x y₁ y₂ g).
  Proof.
    exact (rezk_double_rec'_beta_r_rcleq C₁ C₂ hSet _ R _ _ _ _ _ _ _ x g).
  Qed.
End rezk_relation.
