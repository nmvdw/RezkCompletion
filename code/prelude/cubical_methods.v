Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(** We look at heterogeneous equality.
    This is equality between inhabitants of different types.
    We follow the paper 'Cubical Methods in SYnthetic Homotopy Theory.
 *)

Definition PathOver_to_path
           {A : UU} {C : A → UU}
           {a₁ a₂ : A} {p : a₁ = a₂}
           {c₁ : C a₁} {c₂ : C a₂}
           (q : PathOver p c₁ c₂)
  : transportf C p c₁ = c₂.
Proof.
  induction p.
  exact q.
Defined.

Definition path_to_PathOver
           {A : UU} {C : A → UU}
           {a₁ a₂ : A} {p : a₁ = a₂}
  : ∏ {c₁ : C a₁} {c₂ : C a₂} (q : transportf C p c₁ = c₂),
    PathOver p c₁ c₂.
Proof.
  induction p.
  exact (λ _ _ q, q).
Defined.

Definition PathOver_to_path_isweq
           {A : UU} {C : A → UU}
           {a₁ a₂ : A} (p : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : isweq (@PathOver_to_path A C a₁ a₂ p c₁ c₂).
Proof.
  use isweq_iso.
  - exact path_to_PathOver.
  - intros q.
    induction p.
    apply idpath.
  - intros q.
    induction p.
    apply idpath.
Defined.

Section operations.
  (** A path in a dependent family gives a path in a sigma type. *)
  Definition path_prod_po
             {A : UU} {C : A → UU}
             {a₁ a₂ : A} (p : a₁ = a₂)
             {c₁ : C a₁} {c₂ : C a₂}
             (q : PathOver p c₁ c₂)
    : (a₁ ,, c₁) = (a₂ ,, c₂).
  Proof.
    induction p.
    induction q.
    exact (idpath _).
  Defined.
  
  (** If the fiber is constant, then it is just a path in that fiber. *)
  Definition PathOver_const
             {A C : UU}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ c₂ : C}
             (q : PathOver p c₁ c₂)
    : c₁ = c₂.
  Proof.
    induction p.
    exact q.
  Defined.

  Definition path_over_const_isweq
         {A C : UU}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ c₂ : C}
    : isweq (@PathOver_const A C a₁ a₂ p c₁ c₂).
  Proof.
    use isweq_iso.
    - exact (PathOverConstant_map1 p).
    - intros q.
      induction p.
      exact (idpath q).
    - intros q.
      induction p.
      exact (idpath q).      
  Defined.

  (** Composing the fibration with a map [f] gives a path over [ap f p]. *)
  Definition PathOver_compose
             {A B : UU} {C : B → UU} (f : A → B)
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ : C (f a₁)} {c₂ : C (f a₂)}
             (q : @PathOver _ _ _ p (λ z, C(f z)) c₁ c₂)
    : @PathOver _ _ _ (maponpaths f p) C c₁ c₂.
  Proof.
    induction p.
    exact q.
  Defined.

  Definition compose_PathOver
             {A B : UU} {C : B → UU} (f : A → B)
             {a₁ a₂ : A} {p : a₁ = a₂}
    : ∏ {c₁ : C (f a₁)} {c₂ : C (f a₂)}
        (q : @PathOver _ _ _ (maponpaths f p) C c₁ c₂),
      @PathOver _ _ _ p (λ z, C(f z)) c₁ c₂.
  Proof.
    induction p.
    exact (λ _ _ q, q).
  Defined.

  Definition PathOver_compose_isweq
         {A B : UU} {C : B → UU} (f : A → B)
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ : C (f a₁)} {c₂ : C (f a₂)}
    : isweq (@PathOver_compose A B C f a₁ a₂ p c₁ c₂).
  Proof.
    use isweq_iso.
    - exact (compose_PathOver f).
    - intros q.
      induction p.
      exact (idpath q).
    - intros q.
      induction p.
      exact (idpath q).
  Defined.
End operations.

(** `const_PathOver` applied to an inverse, gives the inverse in `PathOver`.*)
Definition PathOver_inConstantFamily_inv
           {A C : UU}
           {a₁ a₂ : A} {p : a₁ = a₂}
           {c₁ c₂ : C}
           (q : c₁ = c₂)
  : PathOverConstant_map1 (!p) (!q)
    =
    inversePathOver (PathOverConstant_map1 p q).
Proof.
  induction p.
  exact (idpath (!q)).
Defined.

(** `const_PathOver` applied to a concatanation, gives the concatanation in `PathOver`. *)
Definition PathOver_inConstantFamily_concat
           {A C : UU}
           {a₁ a₂ a₃ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₃}
           {c₁ c₂ c₃ : C}
           (q₁ : c₁ = c₂) (q₂ : c₂ = c₃)
  : PathOverConstant_map1 (p₁ @ p₂) (q₁ @ q₂)
    =
    composePathOver
      (PathOverConstant_map1 p₁ q₁)
      (PathOverConstant_map1 p₂ q₂).
Proof.
  induction p₁, p₂.
  exact (idpath _).
Defined.

(** `apd` on a section of a constant fibration. *)
Definition apd_const
           {A C : UU}
           (f : A → C)
           {a₁ a₂ : A} (p : a₁ = a₂)
  : apd f p = PathOverConstant_map1 p (maponpaths f p).
Proof.
  induction p.
  exact (idpath _).
Defined.

(** `const_PathOver` is injective. *)
Definition PathOver_inConstantFamily_inj
           {A C : UU}
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           {c₁ c₂ : C}
           (q₁ q₂ : c₁ = c₂)
           (h : PathOverConstant_map1 p q₁ = PathOverConstant_map1 p q₂)
  : q₁ = q₂.
Proof.
  induction p.
  exact h.
Defined.

(** `PathOver` in a family of sets. *)
Definition PathOver_hprop
       {A : UU}
       {Y : A → UU}
       (Yisaset : ∏ (a : A), isaset (Y a))
       {a₁ a₂ : A}
       (p : a₁ = a₂)
       (c₁ : Y a₁) (c₂ : Y a₂)
  : isaprop (PathOver p c₁ c₂).
Proof.
  induction p.
  exact (Yisaset _ _ _). 
Defined.

(** `PathOver` in a family of propositions. *)
Definition PathOver_path_hprop
       {A : UU}
       {Y : A → UU}
       (Yisaprop : ∏ (a : A), isaprop (Y a))
       {a₁ a₂ : A}
       (p : a₁ = a₂)
       (c₁ : Y a₁) (c₂ : Y a₂)
  : PathOver p c₁ c₂.
Proof.
  induction p.
  apply Yisaprop.
Defined.

(** `PathOver` in a family of arrows. *)
Definition PathOver_arrow
           {A : UU}
           (Y₁ Y₂ : A → UU)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (f₁ : Y₁ a₁ → Y₂ a₁) (f₂ : Y₁ a₂ → Y₂ a₂)
           (q : ∏ (x : Y₁ a₂), PathOver p (f₁ (transportb _ p x)) (f₂ x))
  : @PathOver _ _ _ p (λ a, Y₁ a → Y₂ a) f₁ f₂.
Proof.
  induction p.
  use funextsec.
  intro x.
  apply q.
Defined.

(** A globe represents an equality between two paths. *)
Definition globe
           {A : UU}
  : ∏ {a₁ a₂ : A} (p q : a₁ = a₂), UU
  := λ _ _ p q, p = q.

(** We can also define `globe_over`, which represents an equality between two `PathOver`. *)
Definition globe_over
           {A : UU}
           (Y : A → UU)
           {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           (q₁ : PathOver p₁ c₁ c₂)
           (q₂ : PathOver p₂ c₁ c₂)
  : UU
  := PathOver_to_path
       (transportf
          (λ z, PathOver z c₁ c₂)
          h
          q₁)
     =
     PathOver_to_path q₂.

(** In a constant fibration, this is the same as proving two paths are equal. *)
Definition const_globe_over
           {A B : UU}
           {a₁ a₂ : A}
           {b₁ b₂ : B}
           {p₁ p₂ : a₁ = a₂}
           (h₁ : globe p₁ p₂)
           (q₁ q₂ : b₁ = b₂)
           (h₂ : globe q₁ q₂) 
  : globe_over
      (λ _, B) h₁
      (PathOverConstant_map1 _ q₁)
      (PathOverConstant_map1 _ q₂).
Proof.
  induction h₁, h₂.
  apply idpath.
Defined.

(** This changes the sides of a `globe_over`. *)
Definition globe_over_whisker
           {A : UU}
           (Y : A → UU)
           {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           {q₁ q₃ : PathOver p₁ c₁ c₂}
           {q₂ q₄ : PathOver p₂ c₁ c₂}
           (s₁ : q₁ = q₃) (s₂ : q₂ = q₄)
  : globe_over Y h q₁ q₂ → globe_over Y h q₃ q₄.
Proof.
  induction s₁, s₂.
  exact (λ z, z).
Defined.

(** `globe_over` in a family of sets. *)
Definition path_globe_over_hset
           {A : UU}
           {Y : A → UU}
           (Yisaset : ∏ (a : A), isaset (Y a))
           {a₁ a₂ : A}
           {c₁ : Y a₁} {c₂ : Y a₂}
           {p₁ p₂ : a₁ = a₂}
           (h : globe p₁ p₂)
           (q₁ : PathOver p₁ c₁ c₂)
           (q₂ : PathOver p₂ c₁ c₂)
  : globe_over Y h q₁ q₂.
Proof.
  apply Yisaset.
Defined.

(** Squares represents heterogeneous equalities between paths.
    A square has 4 sides `t`, `l`, `r`, `d` and it represents `l^ @ t @ r = d`.
 *)
Definition square
           {A : UU}
           {lt rt ld rd : A}
           (t : lt = rt)
           (l : ld = lt) (r : rd = rt)
           (d : ld = rd)
  : UU
  := l @ t = d @ r.

(** A square is a path over a pair of paths in a family of paths. *)
Definition square_to_PathOver
           {A : UU}
           {lt rt ld rd : A}
           {t : lt = rt}
           {l : ld = lt} {r : rd = rt}
           {d : ld = rd}
           (s : square t l r d)             
  : @PathOver
      (A × A) (ld ,, lt) (rd ,, rt)
      (pathsdirprod d t)
      (λ (x : A × A), pr1 x = pr2 x)
      l r.
Proof.
  induction d.
  induction t ; cbn.
  exact (!(pathscomp0rid l) @ s).
Defined.  

Definition PathOver_to_square
           {X Y : UU}
           {f g : X → Y}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {q₁ : f x₁ = g x₁} {q₂ : f x₂ = g x₂}
           (s : @PathOver _ _ _ p (λ z, f z = g z) q₁ q₂)
  : square q₂ (maponpaths f p) (maponpaths g p) q₁.
Proof.
  induction p, s.
  exact (!(pathscomp0rid _)).
Defined.

Section operations.
  (** We have two identity paths.
      The first one is between the top and bottom side.
   *)
  Definition hrefl
             {A : UU} {a b : A}
             (p : a = b)
    : square p (idpath a) (idpath b) p.
  Proof.
    exact (!(pathscomp0rid _)).
  Defined.

  (** The second identity is between the left and right side. *)
  Definition vrefl
             {A : UU} {a b : A}
             (p : a = b)
    : square (idpath b) p p (idpath a).
  Proof.
    exact (pathscomp0rid p).
  Defined.    

  (** We can apply maps to squares. *)
  Definition ap_square
             {A B : UU} (f : A → B)
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square t l r d)
    : square
        (maponpaths f t)
        (maponpaths f l)
        (maponpaths f r)
        (maponpaths f d).
  Proof.
    exact ((!(maponpathscomp0 _ _ _))
              @ maponpaths (maponpaths f) s
              @ maponpathscomp0 _ _ _).
  Defined.    

  (** We can move a square along paths in each coordinate. *)
  Definition whisker_square
             {A : UU}
             {lt rt ld rd : A}
             {t₁ t₂ : lt = rt}
             {l₁ l₂ : ld = lt} {r₁ r₂ : rd = rt}
             {d₁ d₂ : ld = rd}
             (pt : t₁ = t₂)
             (pl : l₁ = l₂) (pr : r₁ = r₂)
             (pd : d₁ = d₂)
             (s : square t₁ l₁ r₁ d₁)
    : square t₂ l₂ r₂ d₂.
  Proof.
    exact ((maponpaths (λ z, z @ t₂) (!pl))
             @ maponpaths (λ z, l₁ @ z) (!pt)
             @ s
             @ maponpaths (λ z, z @ r₁) pd
             @ maponpaths (λ z, d₂ @ z) pr).
  Defined.

  (** `PathOver` in a family of equations is the same as giving a square. *)
  Definition map_PathOver
             {A B : UU} {f g : A → B}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {l : f a₁ = g a₁} {r : f a₂ = g a₂}
    : square
        r
        (maponpaths f p)
        (maponpaths g p)
        l
      →
      @PathOver
        _ _ _
        p
        (λ z, f z = g z)
        l r.
  Proof.
    intros s.
    apply path_to_PathOver.
    refine (transportf_paths_FlFr _ _ @ _).
    exact (pathsinv0_to_right _ _ _ (!s)).
  Defined.
End operations.
