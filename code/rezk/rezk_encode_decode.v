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

Local Open Scope cat.

Section rezk_iso.
  Variable (C : category).

  Definition iso_right_action
            {x₁ x₂ : C} (y : C)
            (f : z_iso x₁ x₂)
    : z_iso x₁ y → z_iso x₂ y
    := λ h, z_iso_comp (z_iso_inv f) h.

  Definition iso_right_action_inv
            {x₁ x₂ : C} (y : C)
            (g : z_iso x₁ x₂)
    : z_iso x₂ y → z_iso x₁ y
    := λ h, z_iso_comp g h.

  Definition iso_right_action_isweq
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : isweq (iso_right_action x g).
  Proof.
    use gradth.
    - exact (iso_right_action_inv x g).
    - abstract
        (intros h ; cbn ;
         unfold iso_right_action, iso_right_action_inv ; cbn ;
         use z_iso_eq ; cbn ;
         rewrite !assoc ;
         rewrite (z_iso_inv_after_z_iso g) ;
         apply id_left).
    - abstract
        (intros h ; cbn ;
         unfold iso_right_action, iso_right_action_inv ; cbn ;
         use z_iso_eq ; cbn ;
         rewrite !assoc ;
         rewrite (z_iso_after_z_iso_inv g) ;
         apply id_left).
  Defined.

  Definition iso_left_action
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : z_iso x y₁ → z_iso x y₂
    := λ h, z_iso_comp h g.

  Definition iso_left_action_inv
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : z_iso x y₂ → z_iso x y₁
    := λ h, z_iso_comp h (z_iso_inv g).

  Definition iso_left_action_isweq
            (x : C) {y₁ y₂ : C}
            (g : z_iso y₁ y₂)
    : isweq (iso_left_action x g).
  Proof.
    use gradth.
    - exact (iso_left_action_inv x g).
    - abstract
        (intros h ; cbn ;
         unfold iso_left_action, iso_left_action_inv ;
         use z_iso_eq ; cbn ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (z_iso_inv_after_z_iso g)).
    - abstract
        (intros h ; cbn ;
         unfold iso_left_action, iso_left_action_inv ;
         use z_iso_eq ; cbn ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (z_iso_after_z_iso_inv g)).
  Defined.

  (** The action of the unit element is the identity. *)
  Definition iso_left_action_e (x y : C) (g : z_iso x y)
    : iso_left_action x (identity_z_iso y) g = g.
  Proof.
    use z_iso_eq.
    apply id_right.
  Defined.

  Definition iso_right_action_e (x y : C) (g : z_iso x y)
    : iso_right_action y (identity_z_iso x) g = g.
  Proof.
    use z_iso_eq ; cbn.
    apply id_left.
  Qed.

  Definition iso_right_action_comp
            (x₁ x₂ x₃ y : C)
            (g₁ : z_iso x₁ x₂)
            (g₂ : z_iso x₂ x₃)
            (h : z_iso x₁ y)
    : iso_right_action y (z_iso_comp g₁ g₂) h
      =
      iso_right_action y g₂ (iso_right_action y g₁ h).
  Proof.
    use z_iso_eq ; cbn.
    rewrite assoc.
    apply idpath.
  Qed.

  (** The lift of [hom G] to [gquot G]. *)
  Definition r_iso : rezk C → rezk C → hSet.
  Proof.
    simple refine (rezk_relation
                     C C
                     (λ (z₁ z₂ : C), make_hSet (z_iso z₁ z₂) _)
                     (λ _ _ b g, iso_right_action b g)
                     (λ a _ _ g, iso_left_action a g)
                     _ _ _ _ _ _ _).
    - apply isaset_z_iso.
    - intros.
      apply iso_right_action_isweq.
    - intros.
      apply iso_left_action_isweq.
    - intros x y g ; simpl.
      cbn.
      apply iso_right_action_e.
    - intros ; intro ; cbn.
      apply iso_right_action_comp.
    - intros a b g.
      apply iso_left_action_e.
    - intros a b₁ b₂ b₃ g₁ g₂ h ; simpl.
      use z_iso_eq.
      apply assoc.
    - intros a₁ a₂ b₁ b₂ g₁ g₂ h ; simpl.
      use z_iso_eq.
      apply assoc.
  Defined.

  Definition r_iso_l_rcleq
            {x₁ x₂ : C} (y : C) (g : z_iso x₁ x₂)
    : maponpaths (λ z, r_iso z (rcl C y)) (rcleq C g)
      =
      _
    := rezk_relation_beta_l_rcleq
         C C
         (λ (z₁ z₂ : C), make_hSet (z_iso z₁ z₂) _) 
         _ _ _ _ _ _ _ _ _ _ g.

  Definition r_iso_r_rcleq
            (x : C) {y₁ y₂ : C} (g : z_iso y₁ y₂)
    : maponpaths (r_iso (rcl C x)) (rcleq C g)
      =
      _
    := rezk_relation_beta_r_rcleq
         C C
         (λ (z₁ z₂ : C), make_hSet (z_iso z₁ z₂) _) 
         _ _ _ _ _ _ _ _ _ _ g.

  Opaque r_iso.

  Definition r_iso_id : ∏ (x : rezk C), r_iso x x.
  Proof.
    simple refine (rezk_ind_set (λ x, r_iso x x) _ _ _).
    - exact (λ a, identity_z_iso a).
    - intros a₁ a₂ g.
      apply path_to_PathOver.
      refine ((transport_idmap_ap_set (λ x, r_iso x x) (rcleq C g) (identity_z_iso a₁))
                @ _).
      refine (maponpaths (λ z, transportf _ z _) (_ @ _ @ _) @ _).
      + exact (ap_diag2 r_iso (rcleq C g)).
      + refine (maponpaths (λ z, z @ _) (r_iso_r_rcleq a₁ g) @ _).
        exact (maponpaths (λ z, _ @ z) (r_iso_l_rcleq a₂ g)).
      + exact (!(@path_HLevel_comp 2 _ _ _ _ _)).
      + refine (transport_path_hset _ _ @ _) ; simpl.
        unfold iso_right_action, iso_left_action ; simpl.
        use z_iso_eq.
        refine (maponpaths (λ z, _ · z) (id_left _) @ _).
        exact (z_iso_after_z_iso_inv g).
    - intro.
      apply r_iso.
  Defined.

  (** Now we can define the encode function. *)
  Definition encode_rezk (x y : rezk C)
    : x = y → r_iso x y
    := λ p, transportf (r_iso x) p (r_iso_id x).

  (** We can also define the decode function.
      For this we use double induction over a family of sets.
   *)
  Definition decode_rezk (x y : rezk C) : r_iso x y → x = y.
  Proof.
    simple refine (rezk_double_ind_set (λ x y, r_iso x y → x = y) _ _ x y).
    - intros a b.
      use funspace_isaset.
      exact (rtrunc C a b).
    - exact (λ _ _ g, rcleq C g).
    - intros ; simpl.
      simple refine (PathOver_arrow _ _ _ _ _ _) ; simpl.
      intro z.
      apply map_PathOver.
      refine (whisker_square
                (idpath _)
                (!(maponpaths_for_constant_function _ _))
                (!(maponpathsidfun _))               
                (maponpaths
                   (rcleq C)
                   _)
                _).
      + refine (_ @ !(transport_idmap_ap_set (r_iso (rcl C _)) (!(rcleq C g)) z)).
        refine (!(@transport_path_hset
                    (make_hSet (z_iso _ _) _)
                    (make_hSet (z_iso _ _) _)
                    (invweq (make_weq (iso_left_action _ g) (iso_left_action_isweq _ g))) z)
                  @ _).
        refine (maponpaths (λ p, transportf _ p z) _).
        rewrite maponpathsinv0.
        refine (_ @ maponpaths (λ z, ! z) (!(r_iso_r_rcleq _ _))).
        apply (@path_HLevel_inv 2).
      + unfold square ; cbn.
        refine (maponpaths (rcleq C) _ @ rconcat _ _ _).
        use z_iso_eq ; cbn.
        rewrite assoc'.
        rewrite z_iso_after_z_iso_inv.
        exact (!(id_right _)).
    - intros ; simpl.
      simple refine (PathOver_arrow _ _ _ _ _ _).
      intro z ; simpl.
      apply map_PathOver.
      refine (whisker_square
                (idpath _)
                (!(maponpathsidfun _))
                (!(maponpaths_for_constant_function _ _))
                _
                (!(rconcat _ _ _) @ !(pathscomp0rid _))
             ).
      apply maponpaths.
      refine (_ @ !(transport_idmap_ap_set (λ z, r_iso z (rcl C _)) (!(rcleq C g)) z)).
      refine (!(@transport_path_hset
                  (make_hSet (z_iso _ _) _)
                  (make_hSet (z_iso _ _) _)
                  (invweq (make_weq (iso_right_action _ g) (iso_right_action_isweq _ g))) z)
               @ _).
      refine (maponpaths (λ p, transportf pr1hSet p z) _).
      rewrite maponpathsinv0.
      refine (_ @ maponpaths (λ z, !z) (!(r_iso_l_rcleq _ g))).
      apply (@path_HLevel_inv 2).
  Defined.

  (** The encode and decode maps are inverses of each other. *)
  Definition decode_rezk_encode_rezk
            {x y : rezk C}
            (p : x = y)
    : decode_rezk x y (encode_rezk x y p) = p.
  Proof.
    induction p.
    revert x.
    simple refine (rezk_ind_prop _ _ _).
    - intros a ; simpl.
      exact (re _ _).
    - intro.
      exact (rtrunc C _ _ _ _).
  Defined.
  
  Definition encode_rezk_decode_rezk
    : ∏ {x y : rezk C} (p : r_iso x y), encode_rezk x y (decode_rezk x y p) = p.
  Proof.
    simple refine (rezk_double_ind_prop _ _ _).
    - simpl.
      intros a b.
      use impred ; intro.
      exact (setproperty (r_iso _ _) _ _).
    - intros a b g.
      unfold encode_rezk, r_iso_id.
      simpl.
      refine (transport_idmap_ap_set
                (λ x : rezk C, r_iso (rcl C a) x)
                (rcleq C g)
                (identity_z_iso a) @ _).
      rewrite r_iso_r_rcleq.
      rewrite transport_path_hset.
      use z_iso_eq ; cbn.
      apply id_left.
  Defined.

  Definition encode_rezk_isweq
    : ∏ {x y : rezk C}, isweq (encode_rezk x y).
  Proof.
    intros x y.
    use gradth.
    - exact (decode_rezk x y).
    - intros z.
      apply decode_rezk_encode_rezk.
    - intros z.
      apply encode_rezk_decode_rezk.
  Defined.

  Definition encode_rezk_weq
           (x y : rezk C)
    : x = y ≃ r_iso x y.
  Proof.
    use make_weq.
    - exact (encode_rezk x y).
    - apply encode_rezk_isweq.
  Defined.
End rezk_iso.
