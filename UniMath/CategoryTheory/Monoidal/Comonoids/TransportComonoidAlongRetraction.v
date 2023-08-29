(**
Consider a morphism i : B --> a in a monoidal category.
Given a comonoid structure on B, we show how the comonoid structure can be transported to a, provided i is part of a retraction pair (and a compatibility condition).
Furthermore, i becomes a comonoid homomorphism.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.

Local Open Scope cat.
Local Open Scope moncat.

Import ComonoidNotations.

Section TransportingComonoidAlongRetractionPair.

  Context {L : monoidal_cat}.
  Context (B : comonoid L) {a : L} (i : L⟦a,B⟧) (r : L⟦B,a⟧) (ir : is_retraction i r).
  Context (p : i · δ_{B} · (r #⊗ r) · (i #⊗ i) = i · δ_{B}).

  Definition transported_comonoid_comult_data
    : L⟦a, a ⊗ a⟧.
  Proof.
    exact (i · δ_{B} · r #⊗ r).
  Defined.

  Definition transported_comonoid_counit_data
    : L⟦a, monoidal_unit L⟧.
  Proof.
    exact (i · ε_{B}).
  Defined.

  Definition transported_comonoid_data
    : disp_cat_of_comonoids_data L a.
  Proof.
    split.
    - exact transported_comonoid_comult_data.
    - exact transported_comonoid_counit_data.
  Defined.

  Local Lemma diagram_1
    : i · δ_{B} · (r #⊗ r) · (i #⊗ identity a) = i · δ_{B} · identity (pr1 B) #⊗ r.
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact p.
    }
    rewrite ! assoc'.
    do 3 apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply maponpaths.
    apply pathsinv0, ir.
  Qed.

  Local Lemma diagram_2
    : i · δ_{B} · (r #⊗ r) · (identity a #⊗ i) = i · δ_{B} · r #⊗ identity (pr1 B).
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact p.
    }
    rewrite ! assoc'.
    do 3 apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply maponpaths_2.
    apply pathsinv0, ir.
  Qed.

  Lemma transported_comonoid_laws_unit_left
    : comonoid_laws_unit_left L (a,, transported_comonoid_data).
  Proof.
    unfold comonoid_laws_unit_left.
    cbn.
    unfold transported_comonoid_comult_data.

    etrans. {
      apply maponpaths_2.
      unfold transported_comonoid_counit_data.
      rewrite tensor_mor_right.
      rewrite tensor_comp_id_r.
      rewrite assoc.
      apply maponpaths_2.
      apply diagram_1.
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_swap'.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_lunitor.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply maponpaths_2.
      rewrite <- tensor_mor_right.
      apply comonoid_to_law_unit_left.
    }
    rewrite id_left.
    exact ir.
  Qed.

  Lemma transported_comonoid_laws_unit_right
    : comonoid_laws_unit_right L (a,, transported_comonoid_data).
  Proof.
    unfold comonoid_laws_unit_right.
    cbn.
    unfold transported_comonoid_comult_data.

    etrans. {
      apply maponpaths_2.
      unfold transported_comonoid_counit_data.
      rewrite tensor_mor_left.
      rewrite tensor_comp_id_l.
      rewrite assoc.
      apply maponpaths_2.
      apply diagram_2.
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_swap.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_runitor.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply maponpaths_2.
      rewrite <- tensor_mor_left.
      apply comonoid_to_law_unit_right.
    }
    rewrite id_left.
    exact ir.
  Qed.

  Lemma transported_comonoid_laws_assoc
    : comonoid_laws_assoc L (a,, transported_comonoid_data).
  Proof.
    unfold comonoid_laws_assoc.
    cbn.
    unfold transported_comonoid_comult_data.

    rewrite tensor_mor_left.
    rewrite tensor_mor_right.
    rewrite ! tensor_comp_id_l.
    rewrite ! tensor_comp_id_r.
    rewrite ! assoc.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact (! diagram_2).
    }

    etrans. {
      do 3 apply maponpaths_2.
      exact diagram_1.
    }

    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_swap'.
    }

    etrans.
    2: {
      rewrite assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- tensor_mor_left.
      apply comonoid_to_law_assoc.
    }
    rewrite tensor_mor_right.
    rewrite ! assoc'.
    do 2 apply maponpaths.

    rewrite <- tensor_split'.
    etrans.
    2: {
      apply maponpaths.
      apply tensor_lassociator.
    }
    rewrite ! assoc.
    apply maponpaths_2.
    rewrite <- tensor_split.
    do 2 rewrite <- tensor_comp_mor.
    apply maponpaths.
    exact (id_right _ @ ! id_left _).
  Qed.

  Definition transported_comonoid
    : disp_cat_of_comonoids L a.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact transported_comonoid_data.
    - exact transported_comonoid_laws_unit_left.
    - exact transported_comonoid_laws_unit_right.
    - exact transported_comonoid_laws_assoc.
  Defined.

  Definition transported_comonoid_mor
    : comonoid_mor_struct L (a,, transported_comonoid) B i.
  Proof.
    use make_is_comonoid_mor.
    - exact p.
    - apply id_right.
  Qed.

End TransportingComonoidAlongRetractionPair.
