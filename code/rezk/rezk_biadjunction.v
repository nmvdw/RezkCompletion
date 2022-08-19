Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.

Require Import prelude.basics.
Require Import prelude.cubical_methods.
Require Import rezk.rezk.
Require Import rezk.rezk_principles.
Require Import rezk.rezk_encode_decode.
Require Import rezk.rezk_completion.

Local Open Scope cat.

Definition univ_cats_to_cats_data
  : psfunctor_data bicat_of_univ_cats bicat_of_cats.
Proof.
  use make_psfunctor_data.
  - exact (λ C, pr1 C).
  - exact (λ _ _ F, F).
  - exact (λ _ _ _ _ n, n).
  - exact (λ _, nat_trans_id _).
  - exact (λ _ _ _ _ _, nat_trans_id _).
Defined.

Definition univ_cats_to_cats_laws
  : psfunctor_laws univ_cats_to_cats_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ; intro ; cbn ;
    rewrite ?id_left, ?id_right.
  - exact (!(functor_id _ _)).
  - apply idpath.
  - exact (!(functor_id _ _)).
  - apply idpath.
  - apply idpath.
Qed.

Definition univ_cats_to_cats_invertible_cells
  : invertible_cells univ_cats_to_cats_data.
Proof.
  split ; intro ; intros ; use is_nat_z_iso_to_is_invertible_2cell ; intro.
  - apply is_z_isomorphism_identity.
  - apply is_z_isomorphism_identity.
Defined.

Definition univ_cats_to_cats
  : psfunctor bicat_of_univ_cats bicat_of_cats.
Proof.
  use make_psfunctor.
  - exact univ_cats_to_cats_data.
  - exact univ_cats_to_cats_laws.
  - exact univ_cats_to_cats_invertible_cells.
Defined.

Definition left_universal_arrow_univ_cats_to_cats
  : left_universal_arrow univ_cats_to_cats.
Proof.
  use make_left_universal_arrow'.
  - exact univalent_cat_is_univalent_2_1.
  - exact (λ C, rezk_completion_univ_cat C).
  - exact (λ C, rezk_completion_incl C).
  - refine (λ C₁ C₂ F G α, rezk_completion_nat_trans _ α ,, _).
    abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro ;
       apply idpath).
  - intros C₁ C₂ F G α β₁ β₂ p₁ p₂.
    cbn in p₁, p₂.
    use nat_trans_eq ; [ apply homset_property | ].
    use rezk_ind_prop.
    + intro x.
      exact (nat_trans_eq_pointwise p₁ x @ !(nat_trans_eq_pointwise p₂ x)).
    + intro.
      apply homset_property.
  - intros C₁ C₂ F.
    refine (rezk_completion_functor _ F ,, _).
    use nat_z_iso_to_invertible_2cell.
    exact (rezk_completion_commute_nat_z_iso _ F).
Defined.    
