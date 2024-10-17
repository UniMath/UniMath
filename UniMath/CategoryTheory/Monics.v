(** * Monics *)
(** ** Contents
- Definitions of Monics
- Construction of the subcategory of Monics
- Construction of monics in functor categories
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.covyoneda.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Subcategory.Core.

Local Open Scope cat.

(** * Definition of Monics *)
Section def_monic.

  Variable C : category.
  Let hs : has_homsets C := homset_property C.

  (** Definition and construction of isMonic. *)
  Definition isMonic {y z : C} (f : y --> z) : UU :=
    ∏ (x : C) (g h : x --> y), g · f = h · f -> g = h.

  Definition make_isMonic {y z : C} (f : y --> z)
             (H : ∏ (x : C) (g h : x --> y), g · f = h · f -> g = h) : isMonic f := H.

  Lemma isapropisMonic {y z : C} (f : y --> z) : isaprop (isMonic f).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros g.
    apply impred_isaprop; intros h.
    apply impred_isaprop; intros H.
    apply hs.
  Qed.

  (** Definition and construction of Monic. *)
  Definition Monic (y z : C) : UU := ∑ f : y --> z, isMonic f.

  Definition make_Monic {y z : C} (f : y --> z) (H : isMonic f) : Monic y z := tpair _ f H.

  Definition Monic_eq
    {x y : C}
    (f g : Monic x y)
    (H : pr1 f = pr1 g)
    : f = g.
  Proof.
    apply subtypePath.
    - intro.
      apply isapropisMonic.
    - exact H.
  Qed.

  (** Gets the arrow out of Monic. *)
  Definition MonicArrow {y z : C} (M : Monic y z) : C⟦y, z⟧ := pr1 M.
  Coercion MonicArrow : Monic >-> precategory_morphisms.

  Definition MonicisMonic {y z : C} (M : Monic y z) : isMonic M := pr2 M.

  (** Isomorphism to isMonic and Monic. *)
  Lemma is_iso_isMonic {y x : C} (f : y --> x) (H : is_z_isomorphism f) : isMonic f.
  Proof.
    apply make_isMonic.
    intros z g h X.
    apply (post_comp_with_z_iso_is_inj H).
    exact X.
  Qed.

  Lemma is_iso_Monic {y x : C} (f : y --> x) (H : is_z_isomorphism f) : Monic y x.
  Proof.
    apply (make_Monic f (is_iso_isMonic f H)).
  Defined.

  (** Identity to isMonic and Monic. *)
  Lemma identity_isMonic {x : C} : isMonic (identity x).
  Proof.
    apply (is_iso_isMonic (identity x) (is_z_isomorphism_identity x)).
  Defined.

  Lemma identity_Monic {x : C} : Monic x x.
  Proof.
    exact (tpair _ (identity x) (identity_isMonic)).
  Defined.

  (** Composition of isMonics and Monics. *)
  Definition isMonic_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic f -> isMonic g -> isMonic (f · g).
  Proof.
    intros X X0. apply make_isMonic. intros x0 g0 h X1.
    repeat rewrite assoc in X1. apply X0 in X1. apply X in X1. apply X1.
  Qed.

  Definition Monic_comp {x y z : C} (M1 : Monic x y) (M2 : Monic y z) :
    Monic x z := tpair _ (M1 · M2) (isMonic_comp M1 M2 (pr2 M1) (pr2 M2)).

  (** If precomposition of g with f is a monic, then f is a monic. *)
  Definition isMonic_postcomp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic (f · g) -> isMonic f.
  Proof.
    intros X. intros w φ ψ H.
    apply (maponpaths (λ f', f' · g)) in H.
    repeat rewrite <- assoc in H.
    apply (X w _ _ H).
  Defined.

  Lemma isMonic_path {x y : C} (f1 f2 : x --> y) (e : f1 = f2) (isM : isMonic f1) : isMonic f2.
  Proof.
    induction e. exact isM.
  Qed.

  (** Transport of isMonic *)
  Lemma transport_target_isMonic {x y z : C} (f : x --> y) (E : isMonic f) (e : y = z) :
    isMonic (transportf (precategory_morphisms x) e f).
  Proof.
    induction e. apply E.
  Qed.

  Lemma transport_source_isMonic {x y z : C} (f : y --> z) (E : isMonic f) (e : y = x) :
    isMonic (transportf (λ x' : ob C, precategory_morphisms x' z) e f).
  Proof.
    induction e. apply E.
  Qed.

End def_monic.
Arguments isMonic [C] [y] [z] _.


(** * Construction of the subcategory consisting of all monics. *)
Section monics_subcategory.

  Variable C : category.
  Let hs : has_homsets C := homset_property C.

  Definition hsubtype_obs_isMonic : hsubtype C := (λ c : C, make_hProp _ isapropunit).

  Definition hsubtype_mors_isMonic : ∏ (a b : C), hsubtype (C⟦a, b⟧) :=
    (λ a b : C, (fun f : C⟦a, b⟧ => make_hProp _ (isapropisMonic C f))).

  Definition subprecategory_of_monics : sub_precategories C.
  Proof.
    use tpair.
    split.
    - exact hsubtype_obs_isMonic.
    - exact hsubtype_mors_isMonic.
    - cbn. unfold is_sub_precategory. cbn.
      split.
      + intros a tt. exact (identity_isMonic C).
      + apply isMonic_comp.
  Defined.

  Definition has_homsets_subprecategory_of_monics : has_homsets subprecategory_of_monics.
  Proof.
    intros a b.
    apply is_set_sub_precategory_morphisms.
  Qed.

  Definition subcategory_of_monics : category := make_category _ has_homsets_subprecategory_of_monics.

  Definition subprecategory_of_monics_ob (c : C) : ob (subcategory_of_monics) := tpair _ c tt.

  Definition subprecategory_of_monics_mor {c' c : C} (f : c' --> c) (isM : isMonic f) :
    subcategory_of_monics⟦subprecategory_of_monics_ob c', subprecategory_of_monics_ob c⟧ :=
    tpair _ f isM.

  (*A morphism (f,,s) in subcategory_of_monics is a z_iso
  if the underlying morphism is also a z_iso,
  because the inverse must be monic.
  *)
  Local Lemma is_z_iso_in_subcategory_of_monics_from_is_z_iso (a b : subcategory_of_monics)
    (f : C⟦ pr1 a , pr1 b ⟧)
    (p : isMonic f) (H : is_z_isomorphism f)
    : is_z_isomorphism (precategory_morphisms_in_subcat f p).
  Proof.
    use make_is_z_isomorphism.
    + use precategory_morphisms_in_subcat.
      - exact (is_z_isomorphism_mor H).
      - use is_iso_isMonic.
        use is_z_isomorphism_inv.
    + induction (is_z_isomorphism_is_inverse_in_precat H) as (H1,H2).
      split.
      - use eq_in_sub_precategory.
        exact H1.
      - use eq_in_sub_precategory.
        exact H2.
  Defined.

  (*The converse of the previous result is always true, see [is_z_iso_from_is_z_iso_in_subcategory]*)
  Definition is_z_iso_in_subcategory_of_monics_weq (a b : subcategory_of_monics)
  (f : a --> b)
  : (is_z_isomorphism (pr1 f)) ≃ (is_z_isomorphism f).
  Proof.
    use weqimplimpl.
    + use is_z_iso_in_subcategory_of_monics_from_is_z_iso.
    + use is_z_iso_from_is_z_iso_in_subcategory.
    + use (isaprop_is_z_isomorphism).
    + use (isaprop_is_z_isomorphism).
  Defined.

  Definition iso_in_subcategory_of_monics_weq (a b : subcategory_of_monics)
    : z_iso (pr1 a) (pr1 b) ≃ z_iso a b.
  Proof.
    use weq_iso.
    - intro f.
      use (make_z_iso _ _ (make_dirprod _ _)).
      + exact (is_iso_Monic _ _ (pr2 f)).
      + exact (is_iso_Monic _ _ (pr2 (z_iso_inv f))).
      + abstract apply Monic_eq, (z_iso_inv_after_z_iso f).
      + abstract apply Monic_eq, (z_iso_after_z_iso_inv f).
    - intro f.
      exact (_ ,, invmap (is_z_iso_in_subcategory_of_monics_weq _ _ _) (pr2 f)).
    - abstract (
        intro f;
        apply z_iso_eq;
        reflexivity
      ).
    - abstract (
        intro f;
        apply z_iso_eq;
        apply Monic_eq;
        reflexivity
      ).
  Defined.

  Definition total2_contr
    {X : UU}
    (P : X → UU)
    (H : ∏ x, iscontr (P x))
    : (∑ x, P x) ≃ X.
  Proof.
    use weq_iso.
    - exact pr1.
    - intro x.
      exact (x ,, iscontrpr1 (H x)).
    - abstract (
        intro x;
        apply subtypePath;
        [ intro;
          apply isapropifcontr;
          apply H
        | reflexivity ]
      ).
    - reflexivity.
  Defined.

  Definition monics_subcategory_paths_weq (a b : subcategory_of_monics)
    : (a = b) ≃ (pr1 a = pr1 b).
  Proof.
    apply (weqonpaths (total2_contr (λ _, unit) (λ _, iscontrunit))).
  Defined.

  Lemma is_univalent_monics_cat
    (H : is_univalent C)
    : is_univalent subcategory_of_monics.
  Proof.
    intros a b.
    use weqhomot.
    - refine (iso_in_subcategory_of_monics_weq _ _ ∘ _)%weq.
      refine (make_weq _ (H _ _) ∘ _)%weq.
      refine (monics_subcategory_paths_weq _ _).
    - intro x.
      induction x.
      apply z_iso_eq.
      apply Monic_eq.
      reflexivity.
  Qed.

End monics_subcategory.


(** * In functor categories monics can be constructed from pointwise monics *)
Section monics_functorcategories.

  Lemma is_nat_trans_monic_from_pointwise_monics (C D : category)
        (F G : ob (functor_category C D)) (α : F --> G) (H : ∏ a : ob C, isMonic (pr1 α a)) :
    isMonic α.
  Proof.
    intros G' β η H'.
    use (nat_trans_eq).
    - apply D.
    - intros x.
      set (H'' := nat_trans_eq_pointwise H' x). cbn in H''.
      apply (H x) in H''.
      exact H''.
  Qed.

  Lemma presheaf_monic_isincl
    {C : category}
    {F G : C ⟶ HSET}
    {α : F ⟹ G}
    (H : isMonic (C := [_, _]) α)
    (X : C)
    : isincl (α X).
  Proof.
    apply (invmap (incl_injectivity _)).
    intros x y.
    refine (pr2 (weqiff (_ ,, _) (setproperty _ _ _) (setproperty _ _ _))).
    intro Hxy.
    do 2 refine (!maponpaths (λ (f : HSET⟦_, _⟧), f _) (functor_id F _) @ !_).
    refine (eqtohomot (nat_trans_eq_pointwise
        (H _ (invmap (covyoneda_weq _ X F) x) (invmap (covyoneda_weq _ X F) y) _)
      X) (identity _)).
    apply nat_trans_eq_alt.
    intro Y.
    apply funextfun.
    intro f.
    do 2 refine (maponpaths (λ (f : HSET⟦_, _⟧), f _) (nat_trans_ax _ _ _ _) @ !_).
    apply (maponpaths (λ x, # G f x)).
    exact Hxy.
  Qed.

End monics_functorcategories.


(** Faithful functors reflect monomorphisms. *)

Lemma faithful_reflects_mono {C D : category} (F : functor C D)
      (FF : faithful F) : reflects_morphism F (@isMonic).
Proof.
  unfold reflects_morphism.
  intros ? ? ? is_monic_Ff.
  intros ? ? ? eqcomp.
  apply (Injectivity (# F)).
  - apply isweqonpathsincl, FF.
  - apply is_monic_Ff.
    refine (!(functor_comp F g f) @ _).
    refine (_ @ functor_comp F h f).
    apply maponpaths; assumption.
Defined.
