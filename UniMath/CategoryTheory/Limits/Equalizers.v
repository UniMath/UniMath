(**

Direct implementation of equalizers together with:

- Definition
- Proof that the equalizer arrow is monic ([EqualizerArrowisMonic])
- Proof that the equalizer arrow of equal morphism
  is an isomorphism ([z_iso_Equalizer_of_same_map])
- Alternative universal property

Written by Tomi Pannila
Extended by Langston Barrett (Nov 2018)

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Retracts.

(** ** Definition *)
Section def_equalizers.

  Context {C : category}.

  (** Definition and construction of isEqualizer. *)
  Definition isEqualizer {x y z : C} (f g : y --> z) (e : x --> y)
             (H : e · f = e · g) : UU :=
    ∏ (w : C) (h : w --> y) (H : h · f = h · g),
      ∃! φ : w --> x, φ · e = h.

  Definition make_isEqualizer {x y z : C} (f g : y --> z) (e : x --> y)
             (H : e · f = e · g) :
    (∏ (w : C) (h : w --> y) (H' : h · f = h · g),
        ∃! ψ : w --> x, ψ · e = h) -> isEqualizer f g e H.
  Proof.
    intros X. unfold isEqualizer. exact X.
  Defined.

  Lemma isaprop_isEqualizer {x y z : C} (f g : y --> z) (e : x --> y)
        (H : e · f = e · g) :
    isaprop (isEqualizer f g e H).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Defined.

  Lemma isEqualizer_path {hs : has_homsets C} {x y z : C} {f g : y --> z} {e : x --> y}
        {H H' : e · f = e · g} (iC : isEqualizer f g e H) :
    isEqualizer f g e H'.
  Proof.
    use make_isEqualizer.
    intros w0 h H'0.
    use unique_exists.
    - exact (pr1 (pr1 (iC w0 h H'0))).
    - exact (pr2 (pr1 (iC w0 h H'0))).
    - intros y0. apply hs.
    - intros y0 X. exact (base_paths _ _ (pr2 (iC w0 h H'0) (tpair _ y0 X))).
  Defined.

  (** Proves that the arrow to the equalizer object with the right
    commutativity property is unique. *)
  Lemma isEqualizerInUnique {x y z : C} (f g : y --> z) (e : x --> y)
        (H : e · f = e · g) (E : isEqualizer f g e H)
        (w : C) (h : w --> y) (H' : h · f = h · g)
        (φ : w --> x) (H'' : φ · e = h) :
    φ = (pr1 (pr1 (E w h H'))).
  Proof.
    set (T := tpair (fun ψ : w --> x => ψ · e = h) φ H'').
    set (T' := pr2 (E w h H') T).
    apply (base_paths _ _ T').
  Defined.

  (** Definition and construction of equalizers. *)
  Definition Equalizer {y z : C} (f g : y --> z) : UU :=
    ∑ e : (∑ w : C, w --> y),
          (∑ H : (pr2 e) · f = (pr2 e) · g, isEqualizer f g (pr2 e) H).

  Definition make_Equalizer {x y z : C} (f g : y --> z) (e : x --> y)
             (H : e · f = e · g) (isE : isEqualizer f g e H) :
    Equalizer f g.
  Proof.
    use tpair.
    - use tpair.
      + apply x.
      + apply e.
    - simpl. exact (tpair _ H isE).
  Defined.

  (** Equalizers in precategories. *)
  Definition Equalizers : UU := ∏ (y z : C) (f g : y --> z), Equalizer f g.
  Definition hasEqualizers : UU := ∏ (y z : C) (f g : y --> z),
      ishinh (Equalizer f g).

  (** Returns the equalizer object. *)
  Definition EqualizerObject {y z : C} {f g : y --> z} (E : Equalizer f g) :
    C := pr1 (pr1 E).
  Coercion EqualizerObject : Equalizer >-> ob.

  (** Returns the equalizer arrow. *)
  Definition EqualizerArrow {y z : C} {f g : y --> z} (E : Equalizer f g) :
    C⟦E, y⟧ := pr2 (pr1 E).

  (** The equality on morphisms that equalizers must satisfy. *)
  Definition EqualizerEqAr {y z : C} {f g : y --> z} (E : Equalizer f g) :
    EqualizerArrow E · f = EqualizerArrow E · g := pr1 (pr2 E).

  (** Returns the property isEqualizer from Equalizer. *)
  Definition isEqualizer_Equalizer {y z : C} {f g : y --> z}
             (E : Equalizer f g) :
    isEqualizer f g (EqualizerArrow E) (EqualizerEqAr E) := pr2 (pr2 E).

  (** Every morphism which satisfy the equalizer equality on morphism factors
    uniquely through the EqualizerArrow. *)
  Definition EqualizerIn {y z : C} {f g : y --> z} (E : Equalizer f g)
             (w : C) (h : w --> y) (H : h · f = h · g) :
    C⟦w, E⟧ := pr1 (pr1 (isEqualizer_Equalizer E w h H)).

  Lemma EqualizerCommutes {y z : C} {f g : y --> z} (E : Equalizer f g)
        (w : C) (h : w --> y) (H : h · f = h · g) :
    (EqualizerIn E w h H) · (EqualizerArrow E) = h.
  Proof.
    exact (pr2 (pr1 ((isEqualizer_Equalizer E) w h H))).
  Defined.

  Lemma isEqualizerInsEq {x y z: C} {f g : y --> z} {e : x --> y}
        {H : e · f = e · g} (E : isEqualizer f g e H)
        {w : C} (φ1 φ2: w --> x) (H' : φ1 · e = φ2 · e) : φ1 = φ2.
  Proof.
    assert (H'1 : φ1 · e · f = φ1 · e · g).
    rewrite <- assoc. rewrite H. rewrite assoc. apply idpath.
    set (E' := make_Equalizer _ _ _ _ E).
    set (E'ar := EqualizerIn E' w (φ1 · e) H'1).
    intermediate_path E'ar.
    apply isEqualizerInUnique. apply idpath.
    apply pathsinv0. apply isEqualizerInUnique. apply pathsinv0. apply H'.
  Defined.

  Lemma EqualizerInsEq {y z: C} {f g : y --> z} (E : Equalizer f g)
        {w : C} (φ1 φ2: C⟦w, E⟧)
        (H' : φ1 · (EqualizerArrow E) = φ2 · (EqualizerArrow E)) : φ1 = φ2.
  Proof.
    apply (isEqualizerInsEq (isEqualizer_Equalizer E) _ _ H').
  Defined.

  Lemma EqualizerInComp {y z : C} {f g : y --> z} (E : Equalizer f g) {x x' : C}
        (h1 : x --> x') (h2 : x' --> y)
        (H1 : h1 · h2 · f = h1 · h2 · g) (H2 : h2 · f = h2 · g) :
    EqualizerIn E x (h1 · h2) H1 = h1 · EqualizerIn E x' h2 H2.
  Proof.
    use EqualizerInsEq. rewrite EqualizerCommutes.
    rewrite <- assoc. rewrite EqualizerCommutes.
    apply idpath.
  Qed.

  (** Morphisms between equalizer objects with the right commutativity
    equalities. *)
  Definition identity_is_EqualizerIn {y z : C} {f g : y --> z}
             (E : Equalizer f g) :
    ∑ φ : C⟦E, E⟧, φ · (EqualizerArrow E) = (EqualizerArrow E).
  Proof.
    exists (identity E).
    apply id_left.
  Defined.

  Lemma EqualizerEndo_is_identity {y z : C} {f g : y --> z} {E : Equalizer f g}
        (φ : C⟦E, E⟧) (H : φ · (EqualizerArrow E) = EqualizerArrow E) :
    identity E = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦E, E⟧ => φ' · _ = _)) φ H).
    assert (H2 : identity_is_EqualizerIn E = H1).
    - apply proofirrelevancecontr.
      apply (isEqualizer_Equalizer E).
      apply EqualizerEqAr.
    - apply (base_paths _ _ H2).
  Defined.

  Definition from_Equalizer_to_Equalizer {y z : C} {f g : y --> z}
             (E E': Equalizer f g) : C⟦E, E'⟧.
  Proof.
    apply (EqualizerIn E' E (EqualizerArrow E)).
    apply EqualizerEqAr.
  Defined.

  Lemma are_inverses_from_Equalizer_to_Equalizer {y z : C} {f g : y --> z}
        {E E': Equalizer f g} :
    is_inverse_in_precat (from_Equalizer_to_Equalizer E E')
                         (from_Equalizer_to_Equalizer E' E).
  Proof.
    split; apply pathsinv0; use EqualizerEndo_is_identity;
    rewrite <- assoc; unfold from_Equalizer_to_Equalizer;
      repeat rewrite EqualizerCommutes; apply idpath.
  Defined.

  Lemma isiso_from_Equalizer_to_Equalizer {y z : C} {f g : y --> z}
        (E E' : Equalizer f g) :
    is_iso (from_Equalizer_to_Equalizer E E').
  Proof.
    apply (is_iso_qinv _ (from_Equalizer_to_Equalizer E' E)).
    apply are_inverses_from_Equalizer_to_Equalizer.
  Defined.

  Definition iso_from_Equalizer_to_Equalizer {y z : C} {f g : y --> z}
             (E E' : Equalizer f g) : iso E E' :=
    tpair _ _ (isiso_from_Equalizer_to_Equalizer E E').

  Lemma z_iso_from_Equalizer_to_Equalizer_inverses {y z : C} {f g : y --> z}
        (E E' : Equalizer f g) :
    is_inverse_in_precat (from_Equalizer_to_Equalizer E E') (from_Equalizer_to_Equalizer E' E).
  Proof.
    use make_is_inverse_in_precat.
    - apply pathsinv0. use EqualizerEndo_is_identity.
      rewrite <- assoc. unfold from_Equalizer_to_Equalizer. rewrite EqualizerCommutes.
      rewrite EqualizerCommutes. apply idpath.
    - apply pathsinv0. use EqualizerEndo_is_identity.
      rewrite <- assoc. unfold from_Equalizer_to_Equalizer. rewrite EqualizerCommutes.
      rewrite EqualizerCommutes. apply idpath.
  Qed.

  Definition z_iso_from_Equalizer_to_Equalizer {y z : C} {f g : y --> z}
             (E E' : Equalizer f g) : z_iso E E'.
  Proof.
    use make_z_iso.
    - exact (from_Equalizer_to_Equalizer E E').
    - exact (from_Equalizer_to_Equalizer E' E).
    - exact (z_iso_from_Equalizer_to_Equalizer_inverses E E').
  Defined.

  (** ** Proof that the equalizer arrow is monic ([EqualizerArrowisMonic]) *)

  (** We prove that EqualizerArrow is a monic. *)
  Lemma EqualizerArrowisMonic {y z : C} {f g : y --> z} (E : Equalizer f g ) :
    isMonic (EqualizerArrow E).
  Proof.
    apply make_isMonic.
    intros z0 g0 h X.
    apply (EqualizerInsEq E).
    apply X.
  Qed.

  Lemma EqualizerArrowMonic {y z : C} {f g : y --> z} (E : Equalizer f g ) :
    Monic _ E y.
  Proof.
    exact (make_Monic C (EqualizerArrow E) (EqualizerArrowisMonic E)).
  Defined.

  (*Definition of the trivial equalizer of f and f*)
  Definition identity_asEqualizer {y z : C} (f : y --> z) : (Equalizer f f).
  Proof.
    use make_Equalizer.
    + exact y.
    + exact (identity y).
    + apply idpath.
    + use make_isEqualizer.
      intros x h p.
      use unique_exists.
      - exact h.
      - use id_right.
      - intro.
        use homset_property.
      - intros t t_tri.
        rewrite <-(id_right t).
        exact t_tri.
  Defined.

  (* The equalizer is a z-isomorphism if f = g *)
  Lemma z_iso_Equalizer_of_same_map {y z : C} {f g : y --> z} (E : Equalizer f g) (p:f = g) : is_z_isomorphism (EqualizerArrow E).
  Proof.
    induction p.
    use (make_is_z_isomorphism _ (from_Equalizer_to_Equalizer (identity_asEqualizer f) E)).
    use z_iso_from_Equalizer_to_Equalizer_inverses.
  Defined.

End def_equalizers.

(** Make the C not implicit for Equalizers *)
Arguments Equalizers : clear implicits.

(** ** Alternative universal property *)

Section Equalizers'.

  Context {C : category} {c d : ob C} (f g : C⟦c, d⟧).
  Context (E : ob C) (h : E --> c) (H : h · f = h · g).

  (** A map into an equalizer can be turned into a map into [c]
      such that its composites with [f] and [g] are equal. *)
  Definition postcomp_with_equalizer_mor (a : ob C) (j : a --> E) :
    ∑ (k : a --> c), (k · f = k · g).
  Proof.
    exists (j · h).
    refine (!assoc _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    assumption.
  Defined.

  Definition isEqualizer' : UU :=
    ∏ (a : ob C), isweq (postcomp_with_equalizer_mor a).

  Definition isEqualizer'_weq (is : isEqualizer') :
    ∏ a, (a --> E) ≃ (∑ k : a --> c, (k · f = k · g)) :=
    λ a, make_weq (postcomp_with_equalizer_mor a) (is a).

  Lemma isaprop_isEqualizer' : isaprop isEqualizer'.
  Proof.
    unfold isEqualizer'.
    apply impred; intro.
    apply isapropisweq.
  Qed.

  (** Can [isEqualizer'_to_isEqualizer] be generalized to arbitrary precategories?

      Compare to [isBinProduct'_to_isBinProduct].
   *)
  Lemma isEqualizer'_to_isEqualizer :
    isEqualizer' -> isEqualizer f g h H.
  Proof.
    intros isEq' E' h' H'.
    apply (@iscontrweqf (hfiber (isEqualizer'_weq isEq' _) (h',, H'))).
    - cbn; unfold hfiber.
      use weqfibtototal; intros j; cbn.
      unfold postcomp_with_equalizer_mor.
      apply subtypeInjectivity.
      intro; apply C.
    - apply weqproperty.
  Defined.

  Lemma isEqualizer_to_isEqualizer' :
    isEqualizer f g h H -> isEqualizer'.
  Proof.
    intros isEq E'.
    unfold postcomp_with_equalizer_mor.
    unfold isweq, hfiber.
    intros hH'.
    apply (@iscontrweqf (∑ u : C ⟦ E', E ⟧, u · h = pr1 hH')).
    - use weqfibtototal; intro; cbn.
      apply invweq.
      use subtypeInjectivity.
      intro; apply C.
    - exact (isEq E' (pr1 hH') (pr2 hH')).
  Defined.

  Lemma isEqualizer'_weq_isEqualizer :
    isEqualizer f g h H ≃ isEqualizer'.
  Proof.
    apply weqimplimpl.
    - apply isEqualizer_to_isEqualizer'; assumption.
    - apply isEqualizer'_to_isEqualizer; assumption.
    - apply isaprop_isEqualizer.
    - apply isaprop_isEqualizer'.
  Qed.

End Equalizers'.

Definition isEqualizer_eq
           {C : category}
           {e x y : C}
           {f g f' g' : x --> y}
           {i i' : e --> x}
           (p : i · f = i · g)
           (q : i' · f' = i' · g')
           (s₁ : f = f')
           (s₂ : g = g')
           (s₃ : i = i')
           (He : isEqualizer f g i p)
  : isEqualizer f' g' i' q.
Proof.
  intros w h r.
  use iscontraprop1.
  - abstract
      (induction s₁, s₂, s₃ ;
       apply (isapropifcontr (He w h r))).
  - simple refine (_ ,, _).
    + refine (EqualizerIn (make_Equalizer _ _ _ _ He) _ h _).
      abstract
        (induction s₁, s₂ ;
         exact r).
    + abstract
        (cbn ;
         induction s₁, s₂, s₃ ;
         apply (EqualizerCommutes (make_Equalizer _ _ _ _ He))).
Defined.

(**
 Equalizers are closed under iso
 *)
Lemma isEqualizer_z_iso
           {C : category}
           {e₁ e₂ x y : C}
           {f g : x --> y}
           {p₁ : e₁ --> x}
           {q₁ : p₁ · f = p₁ · g}
           {p₂ : e₂ --> x}
           {q₂ : p₂ · f = p₂ · g}
           (H : isEqualizer f g p₁ q₁)
           (h : z_iso e₂ e₁)
           (r : p₂ = h · p₁)
  : isEqualizer f g p₂ q₂.
Proof.
  intros a k s.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       use (cancel_z_iso _ _ h) ;
       use (isEqualizerInsEq H) ;
       rewrite !assoc' ;
       rewrite <- !r ;
       exact (pr2 φ₁ @ !(pr2 φ₂))).
  - refine (EqualizerIn (make_Equalizer _ _ _ _ H) _ k s · inv_from_z_iso h ,, _).
    abstract
      (rewrite r ;
       rewrite !assoc' ;
       rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)) ;
       refine (maponpaths (λ z, _ · (z · _)) (z_iso_after_z_iso_inv h) @ _) ;
       rewrite id_left ;
       apply (EqualizerCommutes (make_Equalizer _ _ _ _ H))).
Defined.

Lemma Equalizer_eq
  {C : category}
  (E : Equalizers C)
  {x x' y y' : ob C}
  {f g : C⟦x, y⟧}
  {f' g' : C⟦x', y'⟧}
  (i_x : x' = x) (i_y : y = y')
  (p1 : idtoiso i_x · f · idtoiso i_y = f')
  (p2 : idtoiso i_x · g · idtoiso i_y = g')
  : z_iso (E _ _ f g) (E _ _ f' g').
Proof.
  induction i_x, i_y, p1, p2.
  cbn.
  rewrite ! id_left, ! id_right.
  apply identity_z_iso.
Defined.

Section IsEqualizerUnderIso.

  Context {C : category}
  {a a' x x' y y' : ob C}
  {e : C⟦a, x⟧} {f g : C⟦x, y⟧} {p : e · f = e · g}
  {e' : C⟦a', x'⟧} {f' g' : C⟦x', y'⟧}
  (p' : e' · f' = e' · g')
  (i_a : z_iso a a') (i_x : z_iso x x') (i_y : z_iso y y')
  (pd_e : e = i_a · e' · pr1 (pr2 i_x))
  (pd_f : f' · pr1 (pr2 i_y) = pr1 (pr2 i_x) · f)
  (pd_g : g' · pr1 (pr2 i_y) = pr1 (pr2 i_x) · g)
  (E : isEqualizer f g e p).

  Section Aux.

    Context {w : C} {h : C⟦w, x'⟧} (q : h · f' = h · g').

    Lemma t : h · pr1 (pr2 i_x) · f = h · pr1 (pr2 i_x) · g.
    Proof.
      do 2 rewrite assoc'.
      rewrite <- pd_f.
      rewrite <- pd_g.
      rewrite assoc.
      rewrite q.
      apply assoc'.
    Qed.

    Let E' := E w (h · pr1 (pr2 i_x)) t.

    Lemma pfq :  pr1 (pr1 E') · i_a · e' = h.
    Proof.
      pose (pr2 (pr1 E')) as W.
      simpl in W.
      rewrite pd_e in W.
      do 2 rewrite assoc in W.
      pose (z_iso_inv_to_right _ _ _ _ _ _ W) as V.
      refine (_ @ V).
      rewrite ! assoc'.
      do 2 apply maponpaths.
      refine (! id_right _ @ _).
      apply maponpaths, pathsinv0.
      apply (pr2 (pr2 (pr2 i_x))).
    Qed.

    Definition isEqualizerUnderIso_uvp_existence
      : ∑ φ : C ⟦ w, a' ⟧, φ · e' = h
      := pr1 (pr1 E') · i_a ,, pfq.

    Lemma isEqualizerUnderIso_uvp_uniqueness
      : isaprop (∑ φ : C ⟦ w, a' ⟧, φ · e' = h).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath ; [ intro ; apply homset_property | ].
      use (cancel_z_iso _ _ (z_iso_inv i_a)).
      use (isEqualizerInsEq E).
      rewrite !assoc'.
      rewrite ! pd_e.
      etrans. {
        apply maponpaths.
        rewrite ! assoc.
        do 2 apply maponpaths_2.
        refine (_ @ idpath (identity _)).
        apply z_iso_after_z_iso_inv.
      }
      rewrite id_left.
      rewrite assoc.
      rewrite (pr2 φ₁).
      etrans.
      2: {
        apply maponpaths.
        rewrite ! assoc.
        do 2 apply maponpaths_2.
        refine (idpath (identity _) @ _).
        apply pathsinv0, z_iso_after_z_iso_inv.
      }
      rewrite id_left.
      rewrite assoc.
      apply PartA.maponpaths_2.
      exact (!(pr2 φ₂)).
    Qed.

  End Aux.

  Lemma isEqualizerUnderIso : isEqualizer f' g' e' p'.
  Proof.
    intros w h q.
    use iscontraprop1.
    - apply isEqualizerUnderIso_uvp_uniqueness.
    - exact (isEqualizerUnderIso_uvp_existence q).
  Defined.

End IsEqualizerUnderIso.

Section EqualizerOfIso.

  Context {C : category}
    {x' x y y' : ob C}
    (f g : C⟦x, y⟧)
    (i : z_iso x' x)
    (j : z_iso y y')
    (E : Equalizer (i · f · j) (i · g · j)).

  Lemma EqualizerOfIso_diagram_proof
    : EqualizerArrow E · i · f = EqualizerArrow E · i · g.
  Proof.
    use (cancel_z_iso _ _ j) ;
      refine (_ @ EqualizerEqAr E @ _) ;
      [ refine (assoc' _ _ _ @ _) ;
        refine (assoc' _ _ _ @ _) ;
        apply maponpaths ;
        apply assoc
      | refine (_ @ assoc _ _ _);
        refine (_ @ assoc _ _ _);
        apply maponpaths;
        apply assoc'].
  Qed.

  Lemma EqualizerOfIso_diagram_proof_pd_e
    : pr21 E = identity_z_iso E · (EqualizerArrow E · i) · pr12 i.
  Proof.
    apply pathsinv0 ;
      refine (assoc' _ _ _ @ _);
      refine (id_left _ @ _);
      refine (_ @ id_right _);
      refine (assoc' _ _ _ @ _);
      apply maponpaths;
      apply z_iso_inv_after_z_iso.
  Qed.

  Lemma  EqualizerOfIso_diagram_proof_pd_f
    : f · pr12 (z_iso_inv j) = pr12 i · (i · f · j).
  Proof.
    apply pathsinv0.
    do 2 rewrite assoc.
    etrans. {
      do 2 apply maponpaths_2.
      apply (pr2 i).
    }
    refine (assoc' _ _ _ @ _).
    apply id_left.
  Qed.

  Lemma  EqualizerOfIso_diagram_proof_pd_g
    : g · pr12 (z_iso_inv j) = pr12 i · (i · g · j).
  Proof.
    apply pathsinv0.
    do 2 rewrite assoc.
    etrans. {
      do 2 apply maponpaths_2.
      apply (pr2 i).
    }
    refine (assoc' _ _ _ @ _).
    apply id_left.
  Qed.

  Lemma EqualizerOfIso : Equalizer f g.
  Proof.
    use (make_Equalizer f g (EqualizerArrow E · i)).
    - apply EqualizerOfIso_diagram_proof.
    - use (isEqualizerUnderIso _ _ _ _ _ _ _ (pr2 (pr2 E))).
      + apply identity_z_iso.
      + exact i.
      + exact (z_iso_inv j).
      + apply EqualizerOfIso_diagram_proof_pd_e.
      + apply EqualizerOfIso_diagram_proof_pd_f.
      + apply EqualizerOfIso_diagram_proof_pd_g.
  Defined.

End EqualizerOfIso.

(**
 In univalent categories, equalizers are unique up to equality
 *)
Proposition isaprop_Equalizer
            {C : category}
            (HC : is_univalent C)
            {x y : C}
            (f g : x --> y)
  : isaprop (Equalizer f g).
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
    use z_iso_from_Equalizer_to_Equalizer.
  - rewrite transportf_isotoid ; cbn.
    apply EqualizerCommutes.
Qed.

(* For a section-retraction pair (g, f) between b and a, b is the equalizer of id_a and f · g *)
Lemma retract_is_equalizer
  {C : category}
  {a b : C}
  (f : retraction b a)
  : Equalizer (f · retraction_section f) (identity a).
Proof.
  use make_Equalizer.
  - exact b.
  - exact (retraction_section f).
  - abstract (
      refine (_ @ !id_right _);
      refine (assoc _ _ _ @ _);
      refine (maponpaths (λ x, x · _) (retraction_is_retraction f) @ _);
      apply id_left
    ).
  - apply make_isEqualizer.
    intros d f' Hf'.
    use unique_exists.
    + exact (f' · f).
    + abstract exact (assoc' _ _ _ @ Hf' @ id_right _).
    + abstract (
        intro y;
        apply homset_property
      ).
    + abstract (
        intros g' Hg';
        refine (!id_right _ @ _);
        refine (!maponpaths _ (retraction_is_retraction f) @ _);
        refine (assoc _ _ _ @ _);
        apply (maponpaths (λ x, x · _));
        exact Hg'
      ).
Defined.
