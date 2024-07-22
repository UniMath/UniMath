(**************************************************************************************************

  Algebraic theory to Lawvere theory

  Given an algebraic theory T, we can construct a category L with L_0 = nat, and L(m, n) = T_m^n.
  This is functorial in T, and algebraic theory presheaves for T are equivalent to presheaves for L.

  Contents
  1. The functor from algebraic theories to setcategories [algebraic_theory_to_lawvere]
  2. The equivalence between two types of presheaves [algebraic_presheaf_weq_lawere_presheaf]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.PresheafCategory.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope algebraic_theories.
Local Open Scope cat.

(** * 1. The functor from algebraic theories to setcategories *)

Section AlgebraicTheoryToLawvereTheory.

  Section Ob.

    Context (T : algebraic_theory).

    Definition algebraic_theory_to_lawvere_theory_data
      : precategory_data.
    Proof.
      use make_precategory_data.
      - use make_precategory_ob_mor.
        + exact nat.
        + intros m n.
          exact (stn n → (T m : hSet)).
      - intro.
        exact var.
      - intros l m n g f.
        exact (λ i, f i • g).
    Defined.

    Lemma algebraic_theory_to_is_precategory
      : is_precategory algebraic_theory_to_lawvere_theory_data.
    Proof.
      apply make_is_precategory_one_assoc.
      - intros m n f.
        apply funextfun.
        intro i.
        apply subst_var.
      - intros m n f.
        apply funextfun.
        intro i.
        apply var_subst.
      - intros k l m n f g h.
        apply funextfun.
        intro i.
        apply subst_subst.
    Qed.

    Lemma algebraic_theory_to_has_homsets
      : has_homsets algebraic_theory_to_lawvere_theory_data.
    Proof.
      intros m n.
      apply funspace_isaset.
      apply setproperty.
    Qed.

    Lemma algebraic_theory_to_isaset
      : isaset algebraic_theory_to_lawvere_theory_data.
    Proof.
      apply isasetnat.
    Qed.

    Definition algebraic_theory_to_lawvere_ob
      : setcategory
      := make_setcategory
        (make_category
          (make_precategory
            algebraic_theory_to_lawvere_theory_data
            algebraic_theory_to_is_precategory)
          algebraic_theory_to_has_homsets)
        isasetnat.

  End Ob.

  Section Mor.

    Context {T T' : algebraic_theory}.
    Context (f : algebraic_theory_morphism T T').

    Definition algebraic_theory_morphism_to_functor_data
      : functor_data (algebraic_theory_to_lawvere_ob T) (algebraic_theory_to_lawvere_ob T').
    Proof.
      use make_functor_data.
      - exact (idfun nat).
      - intros m n s i.
        exact (f m (s i)).
    Defined.

    Lemma algebraic_theory_morphism_to_is_functor
      : is_functor algebraic_theory_morphism_to_functor_data.
    Proof.
      split.
      - intro n.
        apply funextfun.
        intro i.
        apply mor_var.
      - intros l m n s t.
        apply funextfun.
        intro i.
        apply mor_subst.
    Qed.

    Definition algebraic_theory_morphism_to_functor
      : algebraic_theory_to_lawvere_ob T ⟶ algebraic_theory_to_lawvere_ob T'
      := make_functor _ algebraic_theory_morphism_to_is_functor.

  End Mor.

  Definition algebraic_theory_to_lawvere_functor_data
    : functor_data algebraic_theory_cat cat_of_setcategory
    := make_functor_data (C' := cat_of_setcategory)
      algebraic_theory_to_lawvere_ob
      (λ _ _, algebraic_theory_morphism_to_functor).

  Lemma algebraic_theory_to_lawvere_is_functor
    : is_functor algebraic_theory_to_lawvere_functor_data.
  Proof.
    split.
    - intro T.
      apply (functor_eq _ _ (homset_property _)).
      now use functor_data_eq.
    - intros T T' T'' f f'.
      apply (functor_eq _ _ (homset_property _)).
      now use functor_data_eq.
  Qed.

  Definition algebraic_theory_to_lawvere
    : algebraic_theory_cat ⟶ cat_of_setcategory
    := make_functor _ algebraic_theory_to_lawvere_is_functor.

End AlgebraicTheoryToLawvereTheory.

(** * 2. The equivalence between two types of presheaves *)

Section PresheafEquivalence.

  Context (T : algebraic_theory).

  Definition algebraic_presheaf_to_lawvere_presheaf_ob
    (P : presheaf T)
    : (algebraic_theory_to_lawvere T : setcategory)^op ⟶ SET.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact P.
      + intros m n g f.
        exact (op f g).
    - split.
      + intro n.
        apply funextfun.
        intro p.
        apply op_var.
      + intros l m n f g.
        apply funextfun.
        intro p.
        symmetry.
        apply op_op.
  Defined.

  Definition algebraic_presheaf_to_lawvere_presheaf_mor
    {P P' : presheaf T}
    (f : presheaf_morphism P P')
    : PreShv (algebraic_theory_to_lawvere T : setcategory) ⟦algebraic_presheaf_to_lawvere_presheaf_ob P, algebraic_presheaf_to_lawvere_presheaf_ob P'⟧.
  Proof.
    use make_nat_trans.
    - exact f.
    - intros m n s.
      apply funextfun.
      intro t.
      apply mor_op.
  Defined.

  Definition algebraic_presheaf_to_lawvere_presheaf
    : presheaf_cat T ⟶ PreShv (algebraic_theory_to_lawvere T : setcategory).
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact algebraic_presheaf_to_lawvere_presheaf_ob.
      + exact (λ _ _, algebraic_presheaf_to_lawvere_presheaf_mor).
    - abstract (
        split;
        [ intro P;
          now apply nat_trans_eq_alt
        | intros P P' P'' f g;
          apply nat_trans_eq_alt;
          intro n;
          apply presheaf_mor_comp ]
      ).
  Defined.

  Definition lawvere_presheaf_to_algebraic_presheaf_ob
    (P : (algebraic_theory_to_lawvere T : setcategory)^op ⟶ SET)
    : presheaf T.
  Proof.
    use make_presheaf.
    - use make_presheaf_data.
      + exact P.
      + intros m n a f.
        exact (#P f a).
    - abstract (
        use make_is_presheaf;
        [ intros l m n p f g;
          apply (eqtohomot (!functor_comp P _ _))
        | intros n p;
          apply (eqtohomot (functor_id P _)) ]
      ).
  Defined.

  Definition lawvere_presheaf_to_algebraic_presheaf_mor
    {P P' : (algebraic_theory_to_lawvere T : setcategory)^op ⟶ SET}
    (f : P ⟹ P')
    : presheaf_cat T ⟦lawvere_presheaf_to_algebraic_presheaf_ob P, lawvere_presheaf_to_algebraic_presheaf_ob P'⟧.
  Proof.
    use make_presheaf_morphism.
    - exact f.
    - intros m n a t.
      apply (eqtohomot (nat_trans_ax f _ _ _)).
  Defined.

  Section AlgebraicPresheafIso.

    Context (P : presheaf T).

    Definition algebraic_presheaf_iso_mor
      : presheaf_cat T ⟦lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P), P⟧.
    Proof.
      use make_presheaf_morphism.
      - intro n.
        apply idfun.
      - abstract easy.
    Defined.

    Definition algebraic_presheaf_iso_inv
      : presheaf_cat T ⟦P, lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P)⟧.
    Proof.
      use make_presheaf_morphism.
      - intro n.
        apply idfun.
      - abstract easy.
    Defined.

    Lemma algebraic_presheaf_iso_is_iso
      : is_inverse_in_precat algebraic_presheaf_iso_mor algebraic_presheaf_iso_inv.
    Proof.
      split.
      - apply subtypePath.
        {
          intro.
          use isapropdirprod.
          - do 4 (apply impred_isaprop; intro).
            apply setproperty.
          - apply isapropunit.
        }
        apply funextsec.
        intro n.
        exact (presheaf_mor_comp
          (P := lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P))
          (P'' := lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P))
          _ _ _).
      - apply presheaf_morphism_eq.
        intro n.
        apply presheaf_mor_comp.
    Qed.

    Definition algebraic_presheaf_iso
      : z_iso (C := presheaf_cat T) (lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P)) P
      := make_z_iso
          algebraic_presheaf_iso_mor
          algebraic_presheaf_iso_inv
          algebraic_presheaf_iso_is_iso.

  End AlgebraicPresheafIso.

  Definition lawvere_presheaf_iso
    (P : (algebraic_theory_to_lawvere T : setcategory)^op ⟶ SET)
    : z_iso (C := PreShv (algebraic_theory_to_lawvere T : setcategory)) (algebraic_presheaf_to_lawvere_presheaf_ob (lawvere_presheaf_to_algebraic_presheaf_ob P)) P.
  Proof.
    apply idtoiso.
    apply (functor_eq _ _ (homset_property _)).
    now use functor_data_eq.
  Defined.

  Definition fully_faithful_algebraic_presheaf_to_lawvere_presheaf
    : fully_faithful algebraic_presheaf_to_lawvere_presheaf.
  Proof.
    intros P P'.
    use isweq_iso.
    - intro f.
      exact (inv_from_z_iso (algebraic_presheaf_iso P) · lawvere_presheaf_to_algebraic_presheaf_mor f · algebraic_presheaf_iso P').
    - intro.
      apply (presheaf_morphism_eq (P := (P : presheaf T)) (P' := (P' : presheaf T))).
      intro n.
      refine (presheaf_mor_comp _ _ _ @ _).
      exact (maponpaths (λ x, _ x _) (presheaf_mor_comp _ _ _)).
    - intro.
      apply nat_trans_eq_alt.
      intro n.
      refine (presheaf_mor_comp _ _ _ @ _).
      exact (maponpaths (λ x, _ x _) (presheaf_mor_comp _ _ _)).
  Defined.

  Definition algebraic_presheaf_weq_lawere_presheaf
    : adj_equivalence_of_cats algebraic_presheaf_to_lawvere_presheaf.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_presheaf_cat.
    - exact fully_faithful_algebraic_presheaf_to_lawvere_presheaf.
    - intro P.
      apply hinhpr.
      exists (lawvere_presheaf_to_algebraic_presheaf_ob P).
      apply lawvere_presheaf_iso.
  Defined.

End PresheafEquivalence.
