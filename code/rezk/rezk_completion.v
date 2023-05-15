(**
 In this file, we show that the Rezk completion HIT gives rise
 to a univalent category and we prove its universal property.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import prelude.basics.
Require Import prelude.cubical_methods.
Require Import rezk.rezk.
Require Import rezk.rezk_principles.
Require Import rezk.rezk_encode_decode.

Local Open Scope cat.

Section rezk_completion.
  Variable (C : category).

  Definition right_action
            {x₁ x₂ : C} (y : C)
            (f : z_iso x₁ x₂)
    : x₁ --> y → x₂ --> y
    := λ h, z_iso_inv f · h.

  Definition right_action_inv
            {x₁ x₂ : C} (y : C)
            (g : z_iso x₁ x₂)
    : x₂ --> y → x₁ --> y
    := λ h, g · h.

  Definition right_action_isweq
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : isweq (right_action x g).
  Proof.
    use gradth.
    - exact (right_action_inv x g).
    - abstract
        (intros h ; cbn ;
         unfold right_action, right_action_inv ; cbn ;
         rewrite !assoc ;
         rewrite (z_iso_inv_after_z_iso g) ;
         apply id_left).
    - abstract
        (intros h ; cbn ;
         unfold right_action, right_action_inv ; cbn ;
         rewrite !assoc ;
         rewrite (z_iso_after_z_iso_inv g) ;
         apply id_left).
  Defined.

  Definition left_action
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : x --> y₁ → x --> y₂
    := λ h, h · g.

  Definition left_action_inv
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : x --> y₂ → x --> y₁
    := λ h, h · z_iso_inv g.

  Definition left_action_isweq
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : isweq (left_action x g).
  Proof.
    use gradth.
    - exact (left_action_inv x g).
    - abstract
        (intros h ; cbn ;
         unfold left_action, left_action_inv ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (z_iso_inv_after_z_iso g)).
    - abstract
        (intros h ; cbn ;
         unfold left_action, left_action_inv ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (z_iso_after_z_iso_inv g)).
  Defined.

  (** The action of the unit element is the identity. *)
  Definition left_action_e (x y : C) (g : x --> y)
    : left_action x (identity_z_iso y) g = g.
  Proof.
    apply id_right.
  Defined.

  Definition right_action_e (x y : C) (g : x --> y)
    : right_action y (identity_z_iso x) g = g.
  Proof.
    unfold right_action ; cbn.
    apply id_left.
  Qed.

  Definition right_action_comp
            (x₁ x₂ x₃ y : C)
            (g₁ : z_iso x₁ x₂)
            (g₂ : z_iso x₂ x₃)
            (h : x₁ --> y)
    : right_action y (z_iso_comp g₁ g₂) h = right_action y g₂ (right_action y g₁ h).
  Proof.
    unfold right_action ; cbn.
    rewrite assoc.
    apply idpath.
  Qed.

  (** The lift of [hom G] to [gquot G]. *)
  Definition r_hom : rezk C → rezk C → hSet.
  Proof.
    simple refine (rezk_relation
                     C C
                     (λ (z₁ z₂ : C), make_hSet (z₁ --> z₂) _)
                     (λ _ _ b g, right_action b g)
                     (λ a _ _ g, left_action a g)
                     _ _ _ _ _ _ _).
    - apply homset_property.
    - intros.
      apply right_action_isweq.
    - intros.
      apply left_action_isweq.
    - intros x y g ; simpl.
      cbn.
      apply right_action_e.
    - intros ; intro ; cbn.
      apply right_action_comp.
    - intros a b g.
      apply left_action_e.
    - intros a b₁ b₂ b₃ g₁ g₂ h ; simpl.
      apply assoc.
    - intros a₁ a₂ b₁ b₂ g₁ g₂ h ; simpl.
      apply assoc.
  Defined.

  Definition r_hom_l_rcleq
            {x₁ x₂ : C} (y : C) (g : z_iso x₁ x₂)
    : maponpaths (λ z, r_hom z (rcl C y)) (rcleq C g)
      =
      _
    := rezk_relation_beta_l_rcleq
         C C
         (λ (z₁ z₂ : C), make_hSet (z₁ --> z₂) _) 
         _ _ _ _ _ _ _ _ _ _ g.

  Definition r_hom_r_rcleq
            (x : C) {y₁ y₂ : C} (g : z_iso y₁ y₂)
    : maponpaths (r_hom (rcl C x)) (rcleq C g)
      =
      _
    := rezk_relation_beta_r_rcleq
         C C
         (λ (z₁ z₂ : C), make_hSet (z₁ --> z₂) _) 
         _ _ _ _ _ _ _ _ _ _ g.

  Opaque r_hom.

  Definition r_hom_id : ∏ (x : rezk C), r_hom x x.
  Proof.
    simple refine (rezk_ind_set (λ x, r_hom x x) _ _ _).
    - exact (λ a, identity a).
    - intros a₁ a₂ g.
      apply path_to_PathOver.
      refine ((transport_idmap_ap_set (λ x, r_hom x x) (rcleq C g) (identity a₁))
                @ _).
      refine (maponpaths (λ z, transportf _ z _) (_ @ _ @ _) @ _).
      + exact (ap_diag2 r_hom (rcleq C g)).
      + refine (maponpaths (λ z, z @ _) (r_hom_r_rcleq a₁ g) @ _).
        exact (maponpaths (λ z, _ @ z) (r_hom_l_rcleq a₂ g)).
      + exact (!(@path_HLevel_comp 2 _ _ _ _ _)).
      + refine (transport_path_hset _ _ @ _) ; simpl.
        unfold right_action, left_action ; simpl.
        refine (maponpaths (λ z, _ · z) (id_left _) @ _).
        exact (z_iso_after_z_iso_inv g).
    - intro.
      apply r_hom.
  Defined.

  Definition r_hom_comp
    : ∏ (x y z : rezk C)
        (f : r_hom x y)
        (g : r_hom y z),
      r_hom x z.
  Proof.
    use rezk_triple_ind_set.
    - intros x y z ; cbn.
      do 2 apply funspace_isaset.
      apply r_hom.
    - exact (λ _ _ _ f g, f · g).
    - abstract
        (intros x₁ x₂ y z g ; cbn ;
         use PathOver_arrow ; intro f₁ ;
         use PathOver_arrow ; intro f₂ ;
         apply path_to_PathOver ;
         refine ((transport_idmap_ap_set (λ x, r_hom x _) (rcleq C g) _)
                   @ _) ;
         rewrite r_hom_l_rcleq ;
         rewrite transport_path_hset ;
         rewrite transportb_const ;
         cbn ;
         unfold right_action ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         etrans ;
         [ apply maponpaths ;
           exact (transport_idmap_ap_set (λ x, r_hom x (rcl C y)) (!rcleq C g) _)
         | ] ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_l_rcleq ;
         rewrite <- (@path_HLevel_inv 2) ;
         rewrite transport_path_hset ;
         cbn ;
         unfold right_action_inv ;
         rewrite assoc ;
         rewrite z_iso_after_z_iso_inv ;
         apply id_left).
    - abstract
        (intros x y₁ y₂ z g ; cbn ;
         use PathOver_arrow ; intro f₁ ;
         use PathOver_arrow ; intro f₂ ;
         apply path_to_PathOver ;
         rewrite transportf_const ;
         cbn ;
         etrans ;
         [ apply maponpaths_2 ;
           exact (transport_idmap_ap_set (λ a, r_hom (rcl C x) a) (!(rcleq C g)) _)
         | ] ;
         etrans ;
         [ apply maponpaths ;
           exact (transport_idmap_ap_set (λ a, r_hom a (rcl C z)) (!(rcleq C g)) _)
         | ] ;
         rewrite !maponpathsinv0 ;
         rewrite r_hom_l_rcleq, r_hom_r_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold left_action_inv, right_action_inv ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         rewrite z_iso_inv_after_z_iso ;
         apply id_left).
    - abstract
        (intros x y z₁ z₂ g ; cbn ;
         use PathOver_arrow ; intro f₁ ;
         use PathOver_arrow ; intro f₂ ;
         apply path_to_PathOver ;
         rewrite transportb_const ;
         cbn ;
         refine (transport_idmap_ap_set (λ a, r_hom (rcl C x) a) (rcleq C g) _ @ _) ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (transport_idmap_ap_set (λ a, r_hom (rcl C y) a) (!(rcleq C g)) _)
         | ] ;
         rewrite maponpathsinv0 ;
         rewrite !r_hom_r_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold left_action, left_action_inv ;
         rewrite !assoc' ;
         rewrite z_iso_inv_after_z_iso ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition rezk_completion_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (rezk C).
    - exact r_hom.
  Defined.
  
  Definition rezk_completion_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact rezk_completion_precategory_ob_mor.
    - exact r_hom_id.
    - exact r_hom_comp.
  Defined.

  Definition rezk_completion_is_precategory
    : is_precategory rezk_completion_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - use rezk_double_ind_prop.
      + intros.
        use impred.
        intro.
        apply r_hom.
      + intros x y f.
        apply id_left.
    - use rezk_double_ind_prop.
      + intros.
        use impred.
        intro.
        apply r_hom.
      + intros x y f.
        apply id_right.
    - use rezk_double_ind_prop.
      + intros w x.
        repeat (use impred ; intro).
        apply r_hom.
      + intros w x.
        use rezk_double_ind_prop.
        * intros y z.
          repeat (use impred ; intro).
          apply r_hom.
        * intros y z f g h.
          apply assoc.
  Qed.
  
  Definition rezk_completion_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact rezk_completion_precategory_data.
    - exact rezk_completion_is_precategory.
  Defined.

  Definition rezk_completion
    : category.
  Proof.
    use make_category.
    - exact rezk_completion_precategory.
    - intros x y.
      apply r_hom.
  Defined.

  Definition r_iso_to_r_hom
            {x y : rezk C}
            (f : r_iso C x y)
    : r_hom x y.
  Proof.
    revert x y f.
    use rezk_double_ind_set.
    - intros.
      use funspace_isaset.
      apply r_hom.
    - intros x y f.
      exact (pr1 f).
    - abstract
        (intros x y₁ y₂ g ;
         apply PathOver_arrow ; intro f ;
         apply path_to_PathOver ;
         refine (transport_idmap_ap_set (λ a, r_hom (rcl C x) a) (rcleq C g) _ @ _) ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (transport_idmap_ap_set (λ a, r_iso C (rcl C x) a) (!(rcleq C g)) _)
         | ] ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_r_rcleq ;
         rewrite r_iso_r_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold left_action ;
         rewrite assoc' ;
         rewrite z_iso_after_z_iso_inv ;
         apply id_right).
    - abstract
        (intros x₁ x₂ y g ;
         apply PathOver_arrow ; intro f ;
         apply path_to_PathOver ;
         refine (transport_idmap_ap_set (λ a, r_hom a (rcl C y)) (rcleq C g) _ @ _) ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (transport_idmap_ap_set (λ a, r_iso C a (rcl C y)) (!(rcleq C g)) _)
         | ] ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_l_rcleq ;
         rewrite r_iso_l_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold right_action ;
         rewrite assoc ;
         rewrite z_iso_inv_after_z_iso ;
         apply id_left).
  Defined.

  Definition r_iso_to_r_hom_inv
            {x y : rezk C}
            (f : r_iso C x y)
    : r_hom y x.
  Proof.
    revert x y f.
    use rezk_double_ind_set.
    - intros.
      use funspace_isaset.
      apply r_hom.
    - intros x y f.
      exact (inv_from_z_iso f).
    - abstract
        (intros x y₁ y₂ g ;
         apply PathOver_arrow ; intro f ;
         apply path_to_PathOver ;
         refine (transport_idmap_ap_set (λ a, r_hom a (rcl C x)) (rcleq C g) _ @ _) ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (transport_idmap_ap_set (λ a, r_iso C (rcl C x) a) (!(rcleq C g)) _)
         | ] ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_l_rcleq ;
         rewrite r_iso_r_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold right_action ;
         rewrite assoc ;
         rewrite z_iso_inv_after_z_iso ;
         apply id_left).
    - abstract
        (intros x₁ x₂ y g ;
         apply PathOver_arrow ; intro f ;
         apply path_to_PathOver ;
         refine (transport_idmap_ap_set (λ a, r_hom (rcl C y) a) (rcleq C g) _ @ _) ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (transport_idmap_ap_set (λ a, r_iso C a (rcl C y)) (!(rcleq C g)) _)
         | ] ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_r_rcleq ;
         rewrite r_iso_l_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold left_action ;
         rewrite assoc' ;
         rewrite z_iso_after_z_iso_inv ;
         apply id_right).
  Defined.

  Definition r_iso_to_r_hom_inv_are_invers
            {x y : rezk C}
            (f : r_iso C x y)
    : @is_inverse_in_precat
        rezk_completion
        x y
        (r_iso_to_r_hom f) (r_iso_to_r_hom_inv f).
  Proof.
    split ; revert x y f.
    - use rezk_double_ind_prop.
      + intros x y.
        use impred ; intro.
        apply r_hom.
      + intros x y f.
        exact (z_iso_inv_after_z_iso f).
    - use rezk_double_ind_prop.
      + intros x y.
        use impred ; intro.
        apply r_hom.
      + intros x y f.
        exact (z_iso_after_z_iso_inv f).
  Qed.
  
  Definition r_iso_to_z_iso
           {x y : rezk_completion}
    : r_iso C x y → z_iso x y.
  Proof.
    intro f.
    use make_z_iso.
    - exact (r_iso_to_r_hom f).
    - exact (r_iso_to_r_hom_inv f).
    - exact (r_iso_to_r_hom_inv_are_invers f).
  Defined.

  Definition z_iso_to_r_iso
           {x y : rezk_completion}
    : z_iso x y → r_iso C x y.
  Proof.
    revert x y.
    use rezk_double_ind_set.
    - intros.
      use funspace_isaset.
      apply r_iso.
    - intros x y f ; simpl.
      use make_z_iso.
      + exact (pr1 f).
      + exact (inv_from_z_iso f).
      + split.
        * exact (z_iso_inv_after_z_iso f).
        * exact (z_iso_after_z_iso_inv f).
    - abstract
        (intros x y₁ y₂ g ;
         apply PathOver_arrow ; intro f ;
         apply path_to_PathOver ;
         refine (transport_idmap_ap_set (λ a, r_iso C (rcl C x) a) (rcleq C g) _ @ _) ;
         rewrite r_iso_r_rcleq ;
         rewrite transport_path_hset ;
         use z_iso_eq ;
         cbn ;
         unfold transportb, z_iso ;
         rewrite pr1_transportf ;
         cbn ;
         rewrite (transport_idmap_ap_set (λ a, r_hom (rcl C x) a) (!(rcleq C g)) _) ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_r_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold left_action_inv ;
         rewrite !assoc' ;
         cbn ;
         rewrite z_iso_after_z_iso_inv ;
         apply id_right).
    - abstract
        (intros x₁ x₂ y g ;
         apply PathOver_arrow ; intro f ;
         apply path_to_PathOver ;
         refine (transport_idmap_ap_set (λ a, r_iso C a (rcl C y)) (rcleq C g) _ @ _) ;
         rewrite r_iso_l_rcleq ;
         rewrite transport_path_hset ;
         use z_iso_eq ;
         cbn ;
         unfold transportb, z_iso ;
         rewrite pr1_transportf ;
         cbn ;
         rewrite (transport_idmap_ap_set (λ a, r_hom a (rcl C y)) (!(rcleq C g)) _) ;
         rewrite maponpathsinv0 ;
         rewrite r_hom_l_rcleq ;
         rewrite <- !(@path_HLevel_inv 2) ;
         rewrite !transport_path_hset ;
         cbn ;
         unfold right_action_inv ;
         rewrite !assoc ;
         cbn ;
         rewrite z_iso_after_z_iso_inv ;
         apply id_left).
  Defined.

  Definition r_iso_to_z_iso_to_r_iso
            {x y : rezk_completion}
            (f : r_iso C x y)
    : z_iso_to_r_iso (r_iso_to_z_iso f) = f.
  Proof.
    revert x y f.
    use rezk_double_ind_prop.
    - intros.
      use impred ; intro.
      apply r_iso.
    - intros x y f.
      use z_iso_eq.
      apply idpath.
  Qed.

  Definition z_iso_to_r_iso_to_z_iso
            {x y : rezk_completion}
            (f : z_iso x y)
    : r_iso_to_z_iso (z_iso_to_r_iso f) = f.
  Proof.
    revert x y f.
    use rezk_double_ind_prop.
    - intros.
      use impred;  intro.
      apply isaset_z_iso.
    - intros x y f.
      use z_iso_eq.
      apply idpath.
  Qed.
  
  Definition r_iso_weq_z_iso
           (x y : rezk_completion)
    : r_iso C x y ≃ z_iso x y.
  Proof.
    use make_weq.
    - exact r_iso_to_z_iso.
    - use gradth.
      + exact z_iso_to_r_iso.
      + exact r_iso_to_z_iso_to_r_iso.
      + exact z_iso_to_r_iso_to_z_iso.
  Defined.
  
  Definition is_univalent_rezk_completion
    : is_univalent rezk_completion.
  Proof.
    intros x y.
    use weqhomot.
    - exact (r_iso_weq_z_iso x y ∘ encode_rezk_weq C x y)%weq.
    - intro p.
      induction p.
      use z_iso_eq ; cbn.
      revert x.
      use rezk_ind_prop.
      + intro x.
        apply idpath.
      + intro x.
        simpl.
        apply r_hom.
  Defined.

  Definition rezk_completion_univ_cat
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact rezk_completion.
    - exact is_univalent_rezk_completion.
  Defined.
End rezk_completion.

Definition transportf_functor_2
          {C D : category}
          {F G : C ⟶ D}
          {x₁ x₂ : C}
          (p : x₁ = x₂)
          (f : F x₁ --> G x₁)
  : transportf (λ x, F x --> G x) p f
    =
    #F (transportf (λ z, x₂ --> z) (!p) (identity x₂))
    · f
    · #G (transportf (λ z, x₁ --> z) p (identity x₁)).
Proof.
  induction p ; cbn.
  rewrite !functor_id.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Section universal_property.
  Context (C : category).
  
  Opaque r_hom.
  
  Definition rezk_completion_incl_data
    : functor_data C (rezk_completion C).
  Proof.
    use make_functor_data.
    - exact (λ x, rcl C x).
    - exact (λ x y f, f).
  Defined.

  Definition rezk_completion_incl_is_functor
    : is_functor rezk_completion_incl_data.
  Proof.
    split.
    - intro x.
      apply idpath.
    - intros x y z f g.
      apply idpath.
  Qed.
    
  Definition rezk_completion_incl
    : C ⟶ rezk_completion C.
  Proof.
    use make_functor.
    - exact rezk_completion_incl_data.
    - exact rezk_completion_incl_is_functor.
  Defined.

  Proposition fully_faithful_rezk_completion_incl
    : fully_faithful rezk_completion_incl.
  Proof.
    intros x y.
    use isweq_iso.
    - exact (λ f, f).
    - abstract
        (intro f ;
         apply idpath).
    - abstract
        (intro f ;
         apply idpath).
  Defined.

  Proposition essentially_surjective_rezk_completion_incl
    : essentially_surjective rezk_completion_incl.
  Proof.
    use rezk_ind_prop.
    - intro y ; cbn.
      apply hinhpr.
      refine (y ,, _).
      apply identity_z_iso.
    - intro x.
      apply propproperty.
  Defined.
  
  Section functor.
    Context {D : univalent_category}
           (F : C ⟶ D).

    Definition rezk_completion_functor_ob
      : rezk_completion C → D.
    Proof.
      use rezk_rec.
      - exact (λ z, F z).
      - exact (λ x₁ x₂ f, isotoid _ (pr2 D) (functor_on_z_iso F f)).
      - abstract
          (intro x ; cbn ;
           refine (_ @ isotoid_identity_iso _ (pr2 D) _) ;
           apply maponpaths ;
           use z_iso_eq ;
           apply functor_id).
      - abstract
          (intros x₁ x₂ x₃ f g ; cbn ;
           refine (_ @ isotoid_comp _ _ _ _ _ _ _) ;
           apply maponpaths ;
           use z_iso_eq ;
           apply functor_comp).
      - apply univalent_category_has_groupoid_ob.
    Defined.

    Definition transport_rezk_completion_functor_ob_left
              (x : D)
              {x₁ x₂ : rezk C}
              (p : x₁ = x₂)
              (f : rezk_completion_functor_ob x₁ --> x)
      : transportf
          (λ a : rezk C, rezk_completion_functor_ob a --> x)
          p
          f
        =
        idtoiso (!(maponpaths rezk_completion_functor_ob p)) · f.
    Proof.
      induction p ; cbn.
      exact (!(id_left _)).
    Qed.
    
    Definition transport_rezk_completion_functor_ob_right
              (x : D)
              {x₁ x₂ : rezk C}
              (p : x₁ = x₂)
              (f : x --> rezk_completion_functor_ob x₁)
      : transportf
          (λ a : rezk C, x --> rezk_completion_functor_ob a)
          p
          f
        =
        f · idtoiso (maponpaths rezk_completion_functor_ob p).
    Proof.
      induction p ; cbn.
      exact (!(id_right _)).
    Qed.
    
    Definition rezk_completion_functor_mor
      : ∏ (a b : rezk C)
          (f : r_hom C a b),
        rezk_completion_functor_ob a --> rezk_completion_functor_ob b.
    Proof.
      use rezk_double_ind_set.
      - intros x y.
        use funspace_isaset.
        apply homset_property.
      - exact (λ x y f, # F f).
      - intros x y₁ y₂ f.
        cbn.
        use PathOver_arrow.
        intro g.
        use path_to_PathOver.
        etrans.
        {
          do 2 apply maponpaths.
          unfold transportb.
          simple refine (transport_idmap_ap_set
                           (λ a, r_hom C (rcl C x) a)
                           (!(rcleq C f))
                           _
                         @ _).
          rewrite maponpathsinv0.
          rewrite r_hom_r_rcleq.
          rewrite <- !(@path_HLevel_inv 2).
          rewrite !transport_path_hset.
          cbn.
          unfold left_action_inv.
          apply idpath.
        }
        rewrite transport_rezk_completion_functor_ob_right.
        unfold rezk_completion_functor_ob.
        etrans.
        {
          do 3 apply maponpaths.
          apply rezk_rec_beta_rcleq.
        }
        rewrite idtoiso_isotoid ; cbn.
        rewrite <- functor_comp.
        apply maponpaths.
        rewrite assoc'.
        rewrite z_iso_after_z_iso_inv.
        apply id_right.
      - intros x₁ x₂ y f.
        cbn.
        use PathOver_arrow.
        intro g.
        use path_to_PathOver.
        etrans.
        {
          do 2 apply maponpaths.
          unfold transportb.
          simple refine (transport_idmap_ap_set
                           (λ a, r_hom C a (rcl C y))
                           (!(rcleq C f))
                           _
                         @ _).
          rewrite maponpathsinv0.
          rewrite r_hom_l_rcleq.
          rewrite <- !(@path_HLevel_inv 2).
          rewrite !transport_path_hset.
          cbn.
          unfold left_action_inv.
          apply idpath.
        }
        rewrite transport_rezk_completion_functor_ob_left.
        unfold rezk_completion_functor_ob.
        etrans.
        {
          apply maponpaths_2.
          do 3 apply maponpaths.
          apply rezk_rec_beta_rcleq.
        }
        rewrite idtoiso_inv.
        rewrite idtoiso_isotoid ; unfold right_action_inv ; cbn.
        rewrite <- functor_comp.
        apply maponpaths.
        rewrite assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
    Defined.
    
    Definition rezk_completion_functor_data
      : functor_data (rezk_completion C) D.
    Proof.
      use make_functor_data.
      - exact rezk_completion_functor_ob.
      - exact rezk_completion_functor_mor.
    Defined.

    Definition rezk_completion_is_functor
      : is_functor rezk_completion_functor_data.
    Proof.
      split.
      - use rezk_ind_prop.
        + intro.
          exact (functor_id F x).
        + intro.
          apply homset_property.
      - use rezk_double_ind_prop.
        + intros x y.
          repeat (use impred ; intro).
          apply homset_property.
        + intros x y.
          use rezk_ind_prop.
          * intros z f g.
            exact (functor_comp F f g).
          * intros z.
            repeat (use impred ; intro).
            apply homset_property.
    Qed.
    
    Definition rezk_completion_functor
      : rezk_completion C ⟶ D.
    Proof.
      use make_functor.
      - exact rezk_completion_functor_data.
      - exact rezk_completion_is_functor.
    Defined.

    Definition rezk_completion_commute_nat_trans
      : rezk_completion_incl ∙ rezk_completion_functor ⟹ F.
    Proof.
      use make_nat_trans.
      - exact (λ x, identity _).
      - abstract
          (intros x y f ; simpl ;
           exact (id_right _ @ !(id_left _))).
    Defined.

    Definition rezk_completion_commute_nat_z_iso
      : nat_z_iso
          (rezk_completion_incl ∙ rezk_completion_functor)
          F.
    Proof.
      use make_nat_z_iso.
      - exact rezk_completion_commute_nat_trans.
      - intro.
        apply is_z_isomorphism_identity.
    Defined.
  End functor.

  Section nat_trans.
    Context {D : univalent_category}
           {F G : rezk_completion C ⟶ D}
           (α : rezk_completion_incl ∙ F ⟹ rezk_completion_incl ∙ G).

    Definition rezk_completion_nat_trans_data_po
              {x₁ x₂ : C}
              (f : z_iso x₁ x₂)
      : @PathOver
          _ _ _
          (rcleq C f)
          (λ x, F x --> G x) 
          (α x₁) (α x₂).
    Proof.
      apply path_to_PathOver.
      refine (transportf_functor_2 _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        refine (transport_idmap_ap_set (λ a, r_hom C (rcl C _) a) (rcleq C f) _ @ _).
        rewrite r_hom_r_rcleq.
        rewrite transport_path_hset.
        simpl.
        unfold left_action.
        apply id_left.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        apply maponpaths.
        refine (transport_idmap_ap_set (λ a, r_hom C (rcl C _) a) (!(rcleq C f)) _ @ _).
        rewrite maponpathsinv0.
        rewrite r_hom_r_rcleq.
        rewrite <- !(@path_HLevel_inv 2).
        rewrite transport_path_hset.
        apply id_left.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (nat_trans_ax α _ _ f).
      }
      rewrite !assoc.
      cbn.
      rewrite <- (functor_comp F).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (z_iso_after_z_iso_inv f).
      }
      rewrite (functor_id F).
      apply id_left.
    Qed.
           
    Definition rezk_completion_nat_trans_data
      : nat_trans_data F G.
    Proof.
      use rezk_ind_set.
      - exact (λ x, α x).
      - exact @rezk_completion_nat_trans_data_po.
      - intro.
        apply homset_property.
    Defined.

    Definition rezk_completion_nat_trans_is_nat_trans
      : is_nat_trans F G rezk_completion_nat_trans_data.
    Proof.
      use rezk_double_ind_prop.
      - intros x y.
        use impred ; intro.
        apply homset_property.
      - intros x y f.
        exact (nat_trans_ax α _ _ f).
    Qed.
    
    Definition rezk_completion_nat_trans
      : F ⟹ G.
    Proof.
      use make_nat_trans.
      - exact rezk_completion_nat_trans_data.
      - exact rezk_completion_nat_trans_is_nat_trans.
    Defined.
  End nat_trans.
End universal_property.
