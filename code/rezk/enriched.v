(**********************************************************************************

 Rezk completion for enriched categories as a HIT

 We construct the Rezk completion of enriched categories as a HIT. For this, we use
 the same HIT as for the Rezk completion of ordinary categories.

 Content
 1. Enriched homs
 2. The identity
 3. Composition
 4. Arrows in the enrichment
 5. The laws
 6. The enrichment
 7. Enriched functor to the Rezk completion
 8. Bundled version

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Require Import prelude.basics.
Require Import prelude.cubical_methods.
Require Import rezk.rezk.
Require Import rezk.rezk_principles.
Require Import rezk.rezk_completion.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedRezk.
  Context (V : monoidal_cat)
          (HV : is_univalent V)
          {C : category}
          (E : enrichment C V).

  (** * 1. Enriched homs *)
  Definition enrichment_rezk_completion_hom
    : rezk_completion C → rezk_completion C → V.
  Proof.
    use rezk_double_rec'.
    - abstract
        (exact (univalent_category_has_groupoid_ob (_ ,, HV))).
    - exact (λ x y, E ⦃ x , y ⦄).
    - exact (λ x y₁ y₂ f, isotoid _ HV (postcomp_arr_z_iso _ _ f)).
    - abstract
        (intros x y ; cbn ;
         refine (_ @ isotoid_idtoiso _ HV _ _ _) ;
         apply maponpaths ;
         use z_iso_eq ; cbn ;
         apply postcomp_arr_id).
    - abstract
        (intros x y₁ y₂ y₃ f₁ f₂ ; cbn ;
         refine (_ @ isotoid_idtoiso _ HV _ _ _) ;
         apply maponpaths ;
         rewrite idtoiso_concat ;
         rewrite !idtoiso_isotoid ;
         use z_iso_eq ; cbn ;
         rewrite postcomp_arr_comp ;
         apply idpath).
    - exact (λ x₁ x₂ y f, isotoid _ HV (precomp_arr_z_iso _ _ (z_iso_inv f))).
    - abstract
        (intros x y ; cbn ;
         refine (_ @ isotoid_idtoiso _ HV _ _ _) ;
         apply maponpaths ;
         use z_iso_eq ; cbn ;
         apply precomp_arr_id).
    - abstract
        (intros x y₁ y₂ y₃ f₁ f₂ ; cbn ;
         refine (_ @ isotoid_idtoiso _ HV _ _ _) ;
         apply maponpaths ;
         rewrite idtoiso_concat ;
         rewrite !idtoiso_isotoid ;
         use z_iso_eq ; cbn ;
         rewrite precomp_arr_comp ;
         apply idpath).
    - abstract
        (intros x₁ x₂ y₁ y₂ f₁ f₂ ; cbn ;
         unfold square ;
         refine (!(isotoid_idtoiso _ HV _ _ _) @ _ @ isotoid_idtoiso _ HV _ _ _) ;
         apply maponpaths ;
         rewrite !idtoiso_concat ;
         rewrite !idtoiso_isotoid ;
         use z_iso_eq ; cbn ;
         rewrite precomp_postcomp_arr ;
         apply idpath).
  Defined.

  Proposition enrichment_rezk_completion_hom_beta_l_rcleq
              {x₁ x₂ : C}
              (f : z_iso x₁ x₂)
              (y : C)
    : maponpaths (λ z, enrichment_rezk_completion_hom z (rcl C y)) (rcleq C f)
      =
      isotoid _ HV (precomp_arr_z_iso _ _ (z_iso_inv f)).
  Proof.
    unfold enrichment_rezk_completion_hom.
    apply rezk_double_rec'_beta_l_rcleq.
  Qed.

  Proposition enrichment_rezk_completion_hom_beta_r_rcleq
              (x : C)
              {y₁ y₂ : C}
              (f : z_iso y₁ y₂)
    : maponpaths (λ z, enrichment_rezk_completion_hom (rcl C x) z) (rcleq C f)
      =
      isotoid _ HV (postcomp_arr_z_iso _ _ f).
  Proof.
    unfold enrichment_rezk_completion_hom.
    apply rezk_double_rec'_beta_r_rcleq.
  Qed.

  Proposition enrichment_rezk_completion_hom_beta_lr_rcleq
              {x₁ x₂ : C}
              (f : z_iso x₁ x₂)
    : maponpaths (λ a, enrichment_rezk_completion_hom a a) (rcleq C f)
      =
      isotoid _ HV (z_iso_comp (precomp_arr_z_iso _ _ (z_iso_inv f)) (postcomp_arr_z_iso _ _ f)).
  Proof.
    rewrite maponpaths_diag.
    rewrite enrichment_rezk_completion_hom_beta_r_rcleq.
    rewrite enrichment_rezk_completion_hom_beta_l_rcleq.
    rewrite <- isotoid_comp.
    apply idpath.
  Qed.

  (** * 2. The identity *)
  Definition enrichment_rezk_completion_id
    : ∏ (x : rezk C), I_{V} --> enrichment_rezk_completion_hom x x.
  Proof.
    use rezk_ind_set.
    - exact (λ x, enriched_id E x).
    - abstract
        (intros ;
         use PathOver_mor ;
         rewrite enrichment_rezk_completion_hom_beta_lr_rcleq ;
         rewrite idtoiso_isotoid ;
         rewrite maponpaths_for_constant_function ; cbn ;
         rewrite id_left ;
         rewrite !assoc ;
         rewrite enriched_id_precomp_arr ;
         rewrite enriched_from_arr_postcomp ;
         rewrite z_iso_after_z_iso_inv ;
         rewrite enriched_from_arr_id ;
         apply idpath).
    - abstract
        (intro x ; cbn ;
         apply homset_property).
  Defined.

  (** * 3. Composition *)
  Definition enrichment_rezk_completion_comp
    : ∏ (x y z : rezk C),
      enrichment_rezk_completion_hom y z ⊗ enrichment_rezk_completion_hom x y
      -->
      enrichment_rezk_completion_hom x z.
  Proof.
    use rezk_triple_ind_set.
    - abstract
        (intros ;
         apply homset_property).
    - exact (λ x y z, enriched_comp E x y z).
    - abstract
        (intros x₁ x₂ y z g ;
         use PathOver_mor ; cbn -[enrichment_rezk_completion_hom] ;
         rewrite enrichment_rezk_completion_hom_beta_l_rcleq ;
         rewrite idtoiso_isotoid ;
         refine (!_) ;
         refine (maponpaths
                   (λ z, z · _)
                   (maponpaths_tensor_r
                      (λ z, enrichment_rezk_completion_hom z _)
                      _
                      (rcleq C g))
                 @ _) ;
         rewrite enrichment_rezk_completion_hom_beta_l_rcleq ;
         rewrite idtoiso_isotoid ;
         cbn ;
         rewrite enriched_comp_precomp_arr ;
         apply idpath).
    - abstract
        (intros x y₁ y₂ z g ;
         use PathOver_mor ; cbn -[enrichment_rezk_completion_hom] ;
         rewrite maponpaths_for_constant_function ;
         refine (id_right _ @ _) ;
         refine (!_) ;
         refine (maponpaths
                   (λ z, z · _)
                   (maponpaths_tensor_lr
                      (λ a, enrichment_rezk_completion_hom a _)
                      (λ a, enrichment_rezk_completion_hom _ a)
                      (rcleq C g))
                 @ _) ;
         rewrite enrichment_rezk_completion_hom_beta_l_rcleq ;
         rewrite enrichment_rezk_completion_hom_beta_r_rcleq ;
         rewrite !idtoiso_isotoid ;
         cbn ;
         rewrite tensor_split ;
         rewrite !assoc' ;
         rewrite precomp_postcomp_arr_assoc ;
         rewrite !assoc ;
         refine (_ @ id_left _) ;
         apply maponpaths_2 ;
         rewrite <- tensor_id_id ;
         rewrite <- tensor_comp_id_l ;
         apply maponpaths ;
         rewrite <- postcomp_arr_comp ;
         rewrite z_iso_inv_after_z_iso ;
         apply postcomp_arr_id).
    - abstract
        (intros x y z₁ z₂ g ;
         use PathOver_mor ; cbn -[enrichment_rezk_completion_hom] ;
         rewrite enrichment_rezk_completion_hom_beta_r_rcleq ;
         rewrite idtoiso_isotoid ;
         refine (!_) ;
         refine (maponpaths
                   (λ z, z · _)
                   (maponpaths_tensor_l
                      (enrichment_rezk_completion_hom (rcl C y))
                      (rcleq C g)
                      _)
                 @ _) ;
         rewrite enrichment_rezk_completion_hom_beta_r_rcleq ;
         rewrite idtoiso_isotoid ;
         cbn ;
         rewrite enriched_comp_postcomp_arr ;
         apply idpath).
  Defined.

  (** * 4. Arrows in the enrichment *)
  Definition enrichment_rezk_completion_from_arr
    : ∏ (x y : rezk C),
      r_hom C x y
      →
      I_{V} --> enrichment_rezk_completion_hom x y.
  Proof.
    use rezk_double_ind_set.
    - abstract
        (intros ;
         use impred_isaset ;
         intro ;
         apply homset_property).
    - exact (λ x y f, enriched_from_arr E f).
    - abstract
        (intros x y₁ y₂ g ;
         use PathOver_arrow ;
         intro f ;
         use PathOver_mor ;
         rewrite maponpaths_for_constant_function ;
         refine (_ @ !(id_left _)) ;
         rewrite enrichment_rezk_completion_hom_beta_r_rcleq ;
         rewrite idtoiso_isotoid ;
         refine (enriched_from_arr_postcomp _ _ _ @ _) ;
         apply maponpaths ;
         rewrite functtransportb ;
         rewrite r_hom_r_rcleq ;
         rewrite transport_path_hset' ;
         cbn ;
         unfold left_action_inv ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         exact (z_iso_after_z_iso_inv g)).
    - abstract
        (intros x₁ x₂ y g ;
         use PathOver_arrow ;
         intro f ;
         use PathOver_mor ;
         rewrite maponpaths_for_constant_function ;
         refine (_ @ !(id_left _)) ;
         rewrite enrichment_rezk_completion_hom_beta_l_rcleq ;
         rewrite idtoiso_isotoid ;
         refine (enriched_from_arr_precomp _ _ _ @ _) ;
         apply maponpaths ;
         rewrite functtransportb ;
         rewrite r_hom_l_rcleq ;
         rewrite transport_path_hset' ;
         cbn ;
         unfold right_action_inv ;
         rewrite !assoc ;
         refine (_ @ id_left _) ;
         apply maponpaths_2 ;
         exact (z_iso_after_z_iso_inv g)).
  Defined.

  Definition enrichment_rezk_completion_to_arr
    : ∏ (x y : rezk C),
      I_{V} --> enrichment_rezk_completion_hom x y
      →
      r_hom C x y.
  Proof.
    use rezk_double_ind_set.
    - abstract
        (intros ;
         use impred_isaset ;
         intro ;
         apply setproperty).
    - exact (λ x y f, enriched_to_arr E f).
    - abstract
        (intros x y₁ y₂ g ;
         use PathOver_arrow ;
         intro f ;
         use PathOver_r_hom_l ;
         rewrite functtransportb ;
         rewrite enrichment_rezk_completion_hom_beta_r_rcleq ;
         rewrite transportb_isotoid ;
         rewrite (enriched_to_arr_comp E) ;
         rewrite !enriched_from_to_arr ;
         apply maponpaths ;
         rewrite tensor_comp_l_id_l ;
         rewrite !assoc ;
         rewrite <- tensor_linvunitor ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         cbn ;
         rewrite tensor_split' ;
         rewrite !assoc' ;
         rewrite <- precomp_postcomp_arr_assoc ;
         rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
         rewrite <- tensor_comp_id_r ;
         rewrite enriched_from_arr_precomp ;
         refine (_ @ postcomp_arr_id _ _ _) ;
         unfold postcomp_arr ;
         rewrite !assoc' ;
         apply maponpaths ;
         do 2 apply maponpaths_2 ;
         apply maponpaths ;
         apply z_iso_after_z_iso_inv).
    - abstract
        (intros x₁ x₂ y g ;
         use PathOver_arrow ;
         intro f ;
         use PathOver_r_hom_r ;
         rewrite functtransportb ;
         rewrite enrichment_rezk_completion_hom_beta_l_rcleq ;
         rewrite transportb_isotoid ;
         use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn ;
         rewrite enriched_from_to_arr ;
         rewrite enriched_from_arr_comp ;
         rewrite enriched_from_to_arr ;
         unfold precomp_arr ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         rewrite tensor_split' ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         rewrite mon_linvunitor_I_mon_rinvunitor_I ;
         rewrite <- tensor_rinvunitor ;
         apply idpath).
  Defined.
    
  Definition enrichment_rezk_completion_data
    : enrichment_data (rezk_completion C) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact enrichment_rezk_completion_hom.
    - exact enrichment_rezk_completion_id.
    - exact enrichment_rezk_completion_comp.
    - exact enrichment_rezk_completion_from_arr.
    - exact enrichment_rezk_completion_to_arr.
  Defined.

  (** * 5. The laws *)
  Proposition enrichment_rezk_completion_laws
    : enrichment_laws enrichment_rezk_completion_data.
  Proof.
    repeat split.
    - use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro x.
      use rezk_ind_prop ; [ | intro ; apply homset_property ].
      intro y.
      apply enrichment_id_left.
    - use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro x.
      use rezk_ind_prop ; [ | intro ; apply homset_property ].
      intro y.
      apply enrichment_id_right.
    - use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro w.
      use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro x.
      use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro y.
      use rezk_ind_prop ; [ | intro ; apply homset_property ].
      intro z.
      apply enrichment_assoc.
    - use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro x.
      use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intros y f.
      apply (enriched_to_from_arr E f).
    - use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro x.
      use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intros y f.
      apply (enriched_from_to_arr E f).
    - use rezk_ind_prop ; [ | intro ; apply homset_property ].
      intro x.
      apply (enriched_to_arr_id E x).
    - use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro x.
      use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intro y.
      use rezk_ind_prop ;
        [ | intro ; repeat (use impred ; intro) ; apply homset_property ].
      intros z f g.
      apply (enriched_to_arr_comp E f g).
  Qed.

  (** * 6. The enrichment *)
  Definition enrichment_rezk_completion
    : enrichment (rezk_completion C) V.
  Proof.
    simple refine (_ ,, _).
    - exact enrichment_rezk_completion_data.
    - exact enrichment_rezk_completion_laws.
  Defined.

  (** * 7. Enriched functor to the Rezk completion *)
  Definition enrichment_to_rezk_completion
    : functor_enrichment
        (to_rezk_completion C)
        E
        enrichment_rezk_completion.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (λ x y, identity _).
    - abstract
        (intros x ; cbn ;
         apply id_right).
    - abstract
        (intros x y z ; cbn ;
         rewrite tensor_id_id ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition fully_faithful_enrichment_to_rezk_completion
    : fully_faithful_enriched_functor
        enrichment_to_rezk_completion.
  Proof.
    intros x y ; cbn.
    apply is_z_isomorphism_identity.
  Defined.

  Proposition weak_equivalence_enrichment_to_rezk_completion
    : enriched_weak_equivalence enrichment_to_rezk_completion.
  Proof.
    split.
    - exact (essentially_surjective_to_rezk_completion C).
    - exact fully_faithful_enrichment_to_rezk_completion.
  Defined.

  (** * 8. Bundled version *)
  Definition enriched_rezk_completion_bundled
    : ∑ (RC : univalent_category)
        (ERC : enrichment RC V)
        (F : C ⟶ RC)
        (EF : functor_enrichment F E ERC),
      enriched_weak_equivalence EF
    := rezk_completion_univ_cat C
       ,,
       enrichment_rezk_completion
       ,,
       to_rezk_completion C
       ,,
       enrichment_to_rezk_completion
       ,,
       weak_equivalence_enrichment_to_rezk_completion.
End EnrichedRezk.
