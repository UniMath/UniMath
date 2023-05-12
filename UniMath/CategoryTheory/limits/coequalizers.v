(**

Direct implementation of coequalizers together with:

- Proof that the coequalizer arrow is epi ([CoequalizerArrowisEpi])

Written by Tomi Pannila

*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Section def_coequalizers.

  Context {C : precategory}.

  (** Definition and construction of isCoequalizer. *)
  Definition isCoequalizer {x y z : C} (f g : x --> y) (e : y --> z)
             (H : f · e = g · e) : UU :=
    ∏ (w : C) (h : y --> w) (H : f · h = g · h),
      ∃! φ : z --> w, e · φ  = h.

  Definition make_isCoequalizer {y z w : C} (f g : y --> z) (e : z --> w)
             (H : f · e = g · e) :
    (∏ (w0 : C) (h : z --> w0) (H' : f · h = g · h),
        ∃! ψ : w --> w0, e · ψ = h) -> isCoequalizer f g e H.
  Proof.
    intros X. unfold isCoequalizer. exact X.
  Defined.

  Lemma isaprop_isCoequalizer {y z w : C} (f g : y --> z) (e : z --> w)
        (H : f · e = g · e) :
    isaprop (isCoequalizer f g e H).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Defined.

  Lemma isCoequalizer_path {hs : has_homsets C} {x y z : C} {f g : x --> y} {e : y --> z}
        {H H' : f · e = g · e} (iC : isCoequalizer f g e H) :
    isCoequalizer f g e H'.
  Proof.
    use make_isCoequalizer.
    intros w0 h H'0.
    use unique_exists.
    - exact (pr1 (pr1 (iC w0 h H'0))).
    - exact (pr2 (pr1 (iC w0 h H'0))).
    - intros y0. apply hs.
    - intros y0 X. exact (base_paths _ _ (pr2 (iC w0 h H'0) (tpair _ y0 X))).
  Defined.

  (** Proves that the arrow from the coequalizer object with the right
    commutativity property is unique. *)
  Lemma isCoequalizerOutUnique {y z w: C} (f g : y --> z) (e : z --> w)
        (H : f · e = g · e) (E : isCoequalizer f g e H)
        (w0 : C) (h : z --> w0) (H' : f · h = g · h)
        (φ : w --> w0) (H'' : e · φ = h) :
    φ = (pr1 (pr1 (E w0 h H'))).
  Proof.
    set (T := tpair (fun ψ : w --> w0 => e · ψ = h) φ H'').
    set (T' := pr2 (E w0 h H') T).
    apply (base_paths _ _ T').
  Defined.

  (** Definition and construction of coequalizers. *)
  Definition Coequalizer {y z : C} (f g : y --> z) : UU :=
    ∑ e : (∑ w : C, z --> w),
          (∑ H : f · (pr2 e) = g · (pr2 e), isCoequalizer f g (pr2 e) H).

  Definition make_Coequalizer {y z w : C} (f g : y --> z) (e : z --> w)
             (H : f · e = g · e) (isE : isCoequalizer f g e H) :
    Coequalizer f g.
  Proof.
    use tpair.
    - use tpair.
      + apply w.
      + apply e.
    - simpl. exact (tpair _ H isE).
  Defined.

  (** Coequalizers in precategories. *)
  Definition Coequalizers := ∏ (y z : C) (f g : y --> z),
      Coequalizer f g.

  Definition hasCoequalizers := ∏ (y z : C) (f g : y --> z),
      ishinh (Coequalizer f g).

  (** Returns the coequalizer object. *)
  Definition CoequalizerObject {y z : C} {f g : y --> z} (E : Coequalizer f g) :
    C := pr1 (pr1 E).
  Coercion CoequalizerObject : Coequalizer >-> ob.

  (** Returns the coequalizer arrow. *)
  Definition CoequalizerArrow {y z : C} {f g : y --> z} (E : Coequalizer f g) :
    C⟦z, E⟧ := pr2 (pr1 E).

  (** The equality on morphisms that coequalizers must satisfy. *)
  Definition CoequalizerEqAr {y z : C} {f g : y --> z} (E : Coequalizer f g) :
    f · CoequalizerArrow E = g · CoequalizerArrow E := pr1 (pr2 E).

  (** Returns the property isCoequalizer from Coequalizer. *)
  Definition isCoequalizer_Coequalizer {y z : C} {f g : y --> z}
             (E : Coequalizer f g) :
    isCoequalizer f g (CoequalizerArrow E) (CoequalizerEqAr E) := pr2 (pr2 E).

  (** Every morphism which satisfy the coequalizer equality on morphism factors
    uniquely through the CoequalizerArrow. *)
  Definition CoequalizerOut {y z : C} {f g : y --> z} (E : Coequalizer f g)
             (w : C) (h : z --> w) (H : f · h = g · h) :
    C⟦E, w⟧ := pr1 (pr1 (isCoequalizer_Coequalizer E w h H)).

  Lemma CoequalizerCommutes {y z : C} {f g : y --> z} (E : Coequalizer f g)
        (w : C) (h : z --> w) (H : f · h = g · h) :
    (CoequalizerArrow E) · (CoequalizerOut E w h H) = h.
  Proof.
    exact (pr2 (pr1 ((isCoequalizer_Coequalizer E) w h H))).
  Defined.

  Lemma isCoequalizerOutsEq {y z w: C} {f g : y --> z} {e : z --> w}
        {H : f · e = g · e} (E : isCoequalizer f g e H)
        {w0 : C} (φ1 φ2: w --> w0) (H' : e · φ1 = e · φ2) : φ1 = φ2.
  Proof.
    assert (H'1 : f · e · φ1 = g · e · φ1).
    rewrite H. apply idpath.
    set (E' := make_Coequalizer _ _ _ _ E).
    repeat rewrite <- assoc in H'1.
    set (E'ar := CoequalizerOut E' w0 (e · φ1) H'1).
    intermediate_path E'ar.
    apply isCoequalizerOutUnique. apply idpath.
    apply pathsinv0. apply isCoequalizerOutUnique. apply pathsinv0. apply H'.
  Defined.

  Lemma CoequalizerOutsEq {y z: C} {f g : y --> z} (E : Coequalizer f g)
        {w : C} (φ1 φ2: C⟦E, w⟧)
        (H' : (CoequalizerArrow E) · φ1 = (CoequalizerArrow E) · φ2) :
    φ1 = φ2.
  Proof.
    apply (isCoequalizerOutsEq (isCoequalizer_Coequalizer E) _ _ H').
  Defined.

  Lemma CoequalizerOutComp {y z : C} {f g : y --> z} (CE : Coequalizer f g) {w w' : C}
        (h1 : z --> w) (h2 : w --> w')
        (H1 : f · (h1 · h2) = g · (h1 · h2)) (H2 : f · h1 = g · h1) :
    CoequalizerOut CE w' (h1 · h2) H1 = CoequalizerOut CE w h1 H2 · h2.
  Proof.
    use CoequalizerOutsEq. rewrite CoequalizerCommutes. rewrite assoc.
    rewrite CoequalizerCommutes. apply idpath.
  Qed.

  (** Morphisms between coequalizer objects with the right commutativity
    equalities. *)
  Definition identity_is_CoequalizerOut {y z : C} {f g : y --> z}
             (E : Coequalizer f g) :
    ∑ φ : C⟦E, E⟧, (CoequalizerArrow E) · φ = (CoequalizerArrow E).
  Proof.
    exists (identity E).
    apply id_right.
  Defined.

  Lemma CoequalizerEndo_is_identity {y z : C} {f g : y --> z}
        {E : Coequalizer f g} (φ : C⟦E, E⟧)
        (H : (CoequalizerArrow E) · φ = CoequalizerArrow E) :
    identity E = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦E, E⟧ => _ · φ' = _)) φ H).
    assert (H2 : identity_is_CoequalizerOut E = H1).
    - apply proofirrelevancecontr.
      apply (isCoequalizer_Coequalizer E).
      apply CoequalizerEqAr.
    - apply (base_paths _ _ H2).
  Defined.

  Definition from_Coequalizer_to_Coequalizer {y z : C} {f g : y --> z}
             (E E': Coequalizer f g) : C⟦E, E'⟧.
  Proof.
    apply (CoequalizerOut E E' (CoequalizerArrow E')).
    apply CoequalizerEqAr.
  Defined.

  Lemma are_inverses_from_Coequalizer_to_Coequalizer {y z : C} {f g : y --> z}
        {E E': Coequalizer f g} :
    is_inverse_in_precat (from_Coequalizer_to_Coequalizer E E')
                         (from_Coequalizer_to_Coequalizer E' E).
  Proof.
    split; apply pathsinv0; use CoequalizerEndo_is_identity;
    rewrite assoc; unfold from_Coequalizer_to_Coequalizer;
      repeat rewrite CoequalizerCommutes; apply idpath.
  Defined.

  Lemma isiso_from_Coequalizer_to_Coequalizer {y z : C} {f g : y --> z}
        (E E' : Coequalizer f g) :
    is_iso (from_Coequalizer_to_Coequalizer E E').
  Proof.
    apply (is_iso_qinv _ (from_Coequalizer_to_Coequalizer E' E)).
    apply are_inverses_from_Coequalizer_to_Coequalizer.
  Defined.

  Definition iso_from_Coequalizer_to_Coequalizer {y z : C} {f g : y --> z}
             (E E' : Coequalizer f g) : iso E E' :=
    tpair _ _ (isiso_from_Coequalizer_to_Coequalizer E E').


  (** We prove that CoequalizerArrow is an epi. *)
  Lemma CoequalizerArrowisEpi {y z : C} {f g : y --> z} (E : Coequalizer f g ) :
    isEpi (CoequalizerArrow E).
  Proof.
    apply make_isEpi.
    intros z0 g0 h X.
    apply (CoequalizerOutsEq E).
    apply X.
  Qed.

  Lemma CoequalizerArrowEpi {y z : C} {f g : y --> z} (E : Coequalizer f g ) :
    Epi _ z E.
  Proof.
    exact (make_Epi C (CoequalizerArrow E) (CoequalizerArrowisEpi E)).
  Defined.

End def_coequalizers.

Definition Coequalizer_eq_ar
           {C : category}
           {x y c : C}
           {f g : x --> y}
           {e₁ e₂ : y --> c}
           (p : e₁ = e₂)
           (q₁ : f · e₁ = g · e₁)
           (q₂ : f · e₂ = g · e₂)
           (H : isCoequalizer f g e₁ q₁)
  : isCoequalizer f g e₂ q₂.
Proof.
  induction p.
  use (isCoequalizer_path H).
  apply homset_property.
Defined.

Definition z_iso_to_Coequalizer
           {C : category}
           {x y c₂ : C}
           {f g : x --> y}
           (c₁ : Coequalizer f g)
           (h : z_iso c₁ c₂)
  : Coequalizer f g.
Proof.
  use make_Coequalizer.
  - exact c₂.
  - exact (CoequalizerArrow c₁ · h).
  - abstract
      (rewrite !assoc ;
       rewrite CoequalizerEqAr ;
       apply idpath).
  - intros w k q.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use (cancel_z_iso' h) ;
         use (isCoequalizerOutsEq (pr22 c₁)) ;
         rewrite !assoc ;
         exact (pr2 φ₁ @ !(pr2 φ₂))).
    + refine (inv_from_z_iso h · CoequalizerOut c₁ w k q ,, _).
      abstract
        (rewrite !assoc' ;
         rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)) ;
         rewrite z_iso_inv_after_z_iso ;
         rewrite id_left ;
         rewrite CoequalizerCommutes ;
         apply idpath).
Defined.

Definition z_iso_between_Coequalizer
           {C : category}
           {x y : C}
           {f g : x --> y}
           (c₁ c₂ : Coequalizer f g)
  : z_iso c₁ c₂.
Proof.
  use make_z_iso.
  - exact (CoequalizerOut c₁ c₂ (CoequalizerArrow c₂) (CoequalizerEqAr c₂)).
  - exact (CoequalizerOut c₂ c₁ (CoequalizerArrow c₁) (CoequalizerEqAr c₁)).
  - split.
    + abstract
        (use (isCoequalizerOutsEq (pr22 c₁)) ;
         rewrite id_right ;
         rewrite !assoc ;
         rewrite !CoequalizerCommutes ;
         apply idpath).
    + abstract
        (use (isCoequalizerOutsEq (pr22 c₂)) ;
         rewrite id_right ;
         rewrite !assoc ;
         rewrite !CoequalizerCommutes ;
         apply idpath).
Defined.

(** Make the C not implicit for Coequalizers *)
Arguments Coequalizers : clear implicits.

(**
 In univalent categories, equalizers are unique up to equality
 *)
Proposition isaprop_Coequalizer
            {C : category}
            (HC : is_univalent C)
            {x y : C}
            (f g : x --> y)
  : isaprop (Coequalizer f g).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {
    intro.
    use (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - apply homset_property.
    - simpl.
      repeat (use impred ; intro).
      apply isapropiscontr.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use z_iso_between_Coequalizer.
  - rewrite transportf_isotoid' ; cbn.
    apply CoequalizerCommutes.
Qed.

(**
 A reflexive coequalizer is a coequalizer of two morphisms that
 have a common section. Reflexive coequalizers occur in the
 study of colimits of the Eilenberg-Moore category. More
 specifically, if a monad `M` preserves a class of colimits,
 then the Eilenberg-Moore category has such colimits. However,
 often monads do not preserve all colimits, but only reflexive
 coequalizers. The nice thing about reflexive coequalizers is
 that an Eilenberg-Moore category over a cocomplete category
 is itself cocomplete if and only if it has reflexive
 coequalizers. As such, it suffices to check whether a monad
 preserves reflexive coequalizers in order to guarantee the
 cocompleteness of the Eilenberg-Moore category.
 *)
Definition reflexive_coequalizers
           (C : category)
  : UU
  := ∏ (x y : C)
       (f g : x --> y)
       (h : y --> x)
       (pf : h · f = identity _)
       (pg : h · g = identity _),
     Coequalizer f g.

(**
 If a category has both reflexive coequalizers and binary
 coproducts, then it also has coequalizers.
 *)
Section CoequalizersFromReflexiveCoequalizers.
  Context {C : category}
          (RC : reflexive_coequalizers C)
          (BCC : BinCoproducts C).

  Section CoequalizersFromReflexive.
    Context {x y : C}
            (f g : x --> y).

    Let xy : BinCoproduct x y := BCC x y.

    Let ι₁ : x --> xy := BinCoproductIn1 xy.
    Let ι₂ : y --> xy := BinCoproductIn2 xy.

    Definition coequalizers_from_reflexive_left_map
      : xy --> y
      := BinCoproductArrow xy f (identity _).

    Definition coequalizers_from_reflexive_right_map
      : xy --> y
      := BinCoproductArrow xy g (identity _).

    Let ℓ : xy --> y := coequalizers_from_reflexive_left_map.
    Let ρ : xy --> y := coequalizers_from_reflexive_right_map.

    Lemma coequalizers_from_reflexive_left_map_eq
      : ι₂ · ℓ = identity y.
    Proof.
      apply BinCoproductIn2Commutes.
    Qed.

    Lemma coequalizers_from_reflexive_right_map_eq
      : ι₂ · ρ = identity y.
    Proof.
      apply BinCoproductIn2Commutes.
    Qed.

    Definition coequalizers_from_reflexive_ob
      : Coequalizer ℓ ρ
      := RC _ _
            ℓ ρ
            ι₂
            coequalizers_from_reflexive_left_map_eq
            coequalizers_from_reflexive_right_map_eq.

    Proposition coequalizers_from_reflexive_eq
      : f · CoequalizerArrow coequalizers_from_reflexive_ob
        =
        g · CoequalizerArrow coequalizers_from_reflexive_ob.
    Proof.
      pose (maponpaths
              (λ z, BinCoproductIn1 _ · z)
              (CoequalizerEqAr coequalizers_from_reflexive_ob))
        as p.
      unfold ℓ, ρ in p.
      unfold coequalizers_from_reflexive_left_map in p.
      unfold coequalizers_from_reflexive_right_map in p.
      rewrite !assoc in p.
      rewrite !BinCoproductIn1Commutes in p.
      exact p.
    Qed.

    Section UMP.
      Context {z : C}
              (h : y --> z)
              (p : f · h = g · h).

      Proposition coequalizer_from_reflexive_unique
        : isaprop
            (∑ φ, CoequalizerArrow coequalizers_from_reflexive_ob · φ = h).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use CoequalizerOutsEq.
        exact (pr2 φ₁ @ !(pr2 φ₂)).
      Qed.

      Definition coequalizer_from_reflexive_ump
        : coequalizers_from_reflexive_ob --> z.
      Proof.
        use (CoequalizerOut coequalizers_from_reflexive_ob z h).
        abstract
          (use BinCoproductArrowsEq ;
           unfold ℓ, ρ ;
           unfold coequalizers_from_reflexive_left_map ;
           unfold coequalizers_from_reflexive_right_map ;
           rewrite !assoc ;
           rewrite ?BinCoproductIn1Commutes ;
           rewrite ?BinCoproductIn2Commutes ;
           [ exact p | apply idpath ]).
      Defined.

      Proposition coequalizer_from_reflexive_ump_eq
        : CoequalizerArrow coequalizers_from_reflexive_ob
          · coequalizer_from_reflexive_ump
          =
          h.
      Proof.
        apply CoequalizerCommutes.
      Qed.
    End UMP.

    Definition coequalizer_from_reflexive
      : Coequalizer f g.
    Proof.
      use make_Coequalizer.
      - exact coequalizers_from_reflexive_ob.
      - exact (CoequalizerArrow coequalizers_from_reflexive_ob).
      - exact coequalizers_from_reflexive_eq.
      - intros z h p.
        use iscontraprop1.
        + exact (coequalizer_from_reflexive_unique h).
        + simple refine (_ ,, _).
          * exact (coequalizer_from_reflexive_ump h p).
          * exact (coequalizer_from_reflexive_ump_eq h p).
    Defined.
  End CoequalizersFromReflexive.

  Definition coequalizers_from_reflexive
    : Coequalizers C
    := λ x y f g, coequalizer_from_reflexive f g.
End CoequalizersFromReflexiveCoequalizers.
