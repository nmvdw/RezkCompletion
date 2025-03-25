(**
 The Rezk completion as a higher inductive type

 We define the Rezk completion as a higher inductive type. To
 encode higher inductive types, we use the trick using private
 inductive types. The definition we use corresponds to the
 definition in the HoTT book.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import prelude.cubical_methods.

Local Open Scope cat.

Module Export rezk.
  Private Inductive rezk (C : category) : UU :=
  | rcl : ob C → rezk C.

  Axiom rcleq
    : ∏ (C : category) {x₁ x₂ : C} (f : z_iso x₁ x₂),
      rcl C x₁ = rcl C x₂.

  Axiom re
    : ∏ (C : category) (x : C),
      rcleq C (identity_z_iso x) = idpath (rcl C x).

  Axiom rconcat
    : ∏ (C : category)
        {x₁ x₂ x₃ : C}
        (f₁ : z_iso x₁ x₂) (f₂ : z_iso x₂ x₃),
      rcleq C (z_iso_comp f₁ f₂) = rcleq C f₁ @ rcleq C f₂.

  Definition rinv
    : ∏ (C : category) {x₁ x₂ : C} (f : z_iso x₁ x₂),
      rcleq C (z_iso_inv f) = !(rcleq C f).
  Proof.
    intros C x₁ x₂ f.
    apply path_inverse_from_right.
    rewrite pathsinv0inv0.
    rewrite <- rconcat.
    refine (_ @ re _ x₁).
    apply maponpaths.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_isomorphism.
    }
    exact (z_iso_inv_after_z_iso f).
  Qed.
  
  Axiom rtrunc
    : ∏ (C : category), isofhlevel 3 (rezk C).

  Section rezk_ind.
    Variable (C : category)
            (Y : rezk C → UU)
            (rclY : ∏ (x : C), Y(rcl C x))
            (rcleqY : ∏ (x₁ x₂ : C) (f : z_iso x₁ x₂),
                PathOver (rcleq C f) (rclY x₁) (rclY x₂))
            (reY : ∏ (x : C), globe_over
                                Y
                                (re C x)
                                (rcleqY x x (identity_z_iso x))
                                (idpath (rclY x)))
            (rconcatY : ∏ (x₁ x₂ x₃ : C)
                         (f₁ : z_iso x₁ x₂) (f₂ : z_iso x₂ x₃),
                globe_over
                  Y
                  (rconcat C f₁ f₂)
                  (rcleqY x₁ x₃ (z_iso_comp f₁ f₂))
                  (composePathOver
                     (rcleqY x₁ x₂ f₁)
                     (rcleqY x₂ x₃ f₂)))
            (truncY : ∏ (x : rezk C), isofhlevel 3 (Y x)).
    
    Definition rezk_ind (x : rezk C) : Y x
      := (match x with
         | rcl _ a => fun _ _ _ _ => rclY a
          end) rcleqY reY rconcatY truncY.

    Axiom rezk_ind_beta_rcleq : ∏ (x₁ x₂ : C) (f : z_iso x₁ x₂),
        apd rezk_ind (rcleq C f)
        =
        rcleqY x₁ x₂ f.
  End rezk_ind.
End rezk.

Arguments rezk_ind {C} Y rclY rcleqY reY rconcatY truncY.
