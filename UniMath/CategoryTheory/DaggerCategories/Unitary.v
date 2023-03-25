(* In this file, we have formalized the (correct) notion of isomorphisms in dagger categories, the so called unitary morphisms.
Notice that this definition is different compared to (non-dagger) categories, therefore, we can not reuse is_z_isomorphism. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DaggerCategories.Categories.

Local Open Scope cat.

Section UnitaryMorphisms.

  Definition is_unitary
             {C : category} (dag : dagger_structure C)
             {x y : C} (f : C⟦x,y⟧)
    : UU := is_inverse_in_precat f (dag x y f).

  Lemma isaprop_is_unitary
        {C : category} (dag : dagger_structure C)
        {x y : C} (f : C⟦x,y⟧)
    : isaprop (is_unitary dag f).
  Proof.
    apply isaprop_is_inverse_in_precat.
  Qed.

  Definition unitary {C : category} (dag : dagger_structure C)
             (x y : C)
    : UU
    := ∑ f : C⟦x,y⟧, is_unitary dag f.

  Definition unitary_to_mor
             {C : category} {dag : dagger_structure C}
             {x y : C} (u : unitary dag x y)
    : C⟦x,y⟧ := pr1 u.
  Coercion unitary_to_mor : unitary >-> precategory_morphisms.

  Lemma isaset_unitary
        {C : category} (dag : dagger_structure C) (x y : C)
    : isaset (unitary dag x y).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isaprop_is_unitary.
  Qed.

  Lemma unitary_eq
        {C : category} {dag : dagger_structure C}
        {x y : C}
        (f g : unitary dag x y)
    : pr1 f = pr1 g -> f = g.
  Proof.
    intro p.
    apply (total2_paths_f p).
    apply isaprop_is_unitary.
  Qed.

  Definition unitary_id
             {C : category} (dag : dagger C)
             (x : C)
    : unitary dag x x.
  Proof.
    exists (identity_z_iso x).
    abstract (apply make_is_inverse_in_precat ;
              [ refine (id_left _ @ _) ; apply dagger_to_law_id
              | refine (id_right _ @ _) ; apply dagger_to_law_id ]).
  Defined.

  Lemma is_unitary_comp
             {C : category} {dag : dagger C}
             {x y z : C}
             {f : C⟦x,y⟧} (ff : is_unitary dag f)
             {g : C⟦y,z⟧} (gg : is_unitary dag g)
    : is_unitary dag (f · g).
  Proof.
    split.
    - etrans.
      { apply maponpaths, dagger_to_law_comp. }
      etrans.
      { apply assoc. }
      etrans.
      { apply maponpaths_2, assoc'. }
      etrans.
      { apply maponpaths_2, maponpaths, gg. }
      etrans.
      { apply maponpaths_2, id_right. }
      apply ff.
    - etrans.
      { apply maponpaths_2, dagger_to_law_comp. }
      etrans.
      { apply assoc. }
      etrans.
      { apply maponpaths_2, assoc'. }
      etrans.
      { apply maponpaths_2, maponpaths, ff. }
      etrans.
      { apply maponpaths_2, id_right. }
      apply gg.
  Qed.

  Definition unitary_comp
             {C : category} {dag : dagger C}
             {x y z : C}
             (f : unitary dag x y)
             (g : unitary dag y z)
    : unitary dag x z
    := _ ,, is_unitary_comp (pr2 f) (pr2 g).

  Lemma unitary_inv_is_unitary
             {C : category} {dag : dagger C}
             {x y : C} {f : C⟦x,y⟧}
             (ff : is_unitary dag f)
    : is_unitary dag (pr1 dag x y f).
  Proof.
    split.
    - refine (! dagger_to_law_comp dag y x y (pr1 dag x y f) f @ _).
      etrans.
      { apply maponpaths, ff. }
      apply dagger_to_law_id.
    - refine (! dagger_to_law_comp dag x y x f (pr1 dag x y f) @ _).
      etrans.
      { apply maponpaths, ff. }
      apply dagger_to_law_id.
  Qed.

  Definition unitary_inv
             {C : category} {dag : dagger C}
             {x y : C}
             (f : unitary dag x y)
    : unitary dag y x
    := _ ,, unitary_inv_is_unitary (pr2 f).

  Lemma unitary_inv_of_unitary_inv
        {C : category} {dag : dagger C}
        {x y : C}
        (f : unitary dag x y)
    : unitary_inv (unitary_inv f) = f.
  Proof.
    use unitary_eq.
    apply dagger_to_law_idemp.
  Qed.

End UnitaryMorphisms.

Section EquationalReasoningLemmas.

  Context {C : category} (dag : dagger C).

  Lemma unitary_inv_to_left {a b c : C}
        (f : C⟦ a, b ⟧) (g : C⟦b, c⟧) (h : C⟦ a, c ⟧)
    : is_unitary dag f -> dag _ _ f · h = g → h = f · g.
  Proof.
    exact (λ u p, z_iso_inv_to_left _ _ _ (make_z_iso _ _ (_,,pr2 u)) _ _ p).
  Qed.

  Lemma unitary_inv_on_left {a b c : C}
        (f : C⟦ a, b ⟧) (g : C⟦b, c⟧) (h : C⟦ a, c ⟧)
    : is_unitary dag g -> h = f · g → f = h · dag _ _ g.
  Proof.
    exact (λ u p, z_iso_inv_on_left _ _ _ _ (make_z_iso _ _ (_,,pr2 u)) _ p).
  Qed.

  Lemma unitary_inv_on_right {a b c : C}
        (f : C⟦ a, b ⟧) (g : C⟦b, c⟧) (h : C⟦ a, c ⟧)
    : is_unitary dag f ->  h = f · g → dag _ _ f · h = g.
  Proof.
    exact (λ u p, z_iso_inv_on_right _ _ _ (make_z_iso _ _ (_,,pr2 u)) _ _ p).
  Qed.

  Lemma unitary_inv_to_right {a b c : C}
        (f : C⟦ a, b ⟧) (g : C⟦b, c⟧) (h : C⟦ a, c ⟧)
    : is_unitary dag g ->   f = h · dag _ _ g → f · g = h.
  Proof.
    exact (λ u p, z_iso_inv_to_right _ _ _ _ (make_z_iso _ _ (_,,pr2 u)) _ p).
  Qed.

End EquationalReasoningLemmas.
