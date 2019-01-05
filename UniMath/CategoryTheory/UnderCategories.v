(** Undercategories *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Local Open Scope cat.

Section def_underprecategories.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.
  Variable c : ob C.

  (* Objects *)
  Definition Under_ob : UU := ∑ d, C⟦c, d⟧.

  Definition mk_Under_ob {d : ob C} (f : C⟦c, d⟧) : Under_ob := tpair _ d f.

  (* Accessor functions *)
  Definition Under_ob_cod (X : Under_ob) : ob C := pr1 X.

  Definition Under_ob_mor (X : Under_ob) : C⟦c, Under_ob_cod X⟧ := pr2 X.

  (* Morphisms *)
  Definition Under_mor (X Y : Under_ob) : UU :=
    ∑ f : C⟦Under_ob_cod X, Under_ob_cod Y⟧, Under_ob_mor X · f = Under_ob_mor Y.

  Definition mk_Under_mor (X Y : Under_ob) (f : C⟦Under_ob_cod X, Under_ob_cod Y⟧)
             (H : Under_ob_mor X · f = Under_ob_mor Y) : Under_mor X Y := tpair _ f H.

  (* Accessor functions *)
  Definition Under_mor_mor {X Y : Under_ob} (M : Under_mor X Y) :
    C⟦Under_ob_cod X, Under_ob_cod Y⟧ := pr1 M.

  Definition Under_mor_eq {X Y : Under_ob} (M : Under_mor X Y) :
    Under_ob_mor X · Under_mor_mor M = Under_ob_mor Y := pr2 M.

  (* An undercategory has_homsets *)
  Definition isaset_Under_mor (X Y : Under_ob) : isaset (Under_mor X Y).
  Proof.
    apply (isofhleveltotal2 2).
    - apply hs.
    - intros x.
      apply hlevelntosn.
      apply hs.
  Qed.

  Definition Under_mor_equality (X Y : Under_ob) (f f' : Under_mor X Y) : pr1 f = pr1 f' -> f = f'.
  Proof.
    intro H.
    apply subtypeEquality.
    intro x.
    apply hs.
    exact H.
  Qed.

  Definition Under_id (X : Under_ob) : Under_mor X X := mk_Under_mor X X (identity _) (id_right _ ).

  Local Lemma Under_comp_eq {X Y Z : Under_ob} (f : Under_mor X Y) (g : Under_mor Y Z) :
    Under_ob_mor X · (Under_mor_mor f · Under_mor_mor g) = Under_ob_mor Z.
  Proof.
    rewrite assoc.
    rewrite (Under_mor_eq f).
    exact (Under_mor_eq g).
  Qed.

  Definition Under_comp (X Y Z : Under_ob) : Under_mor X Y -> Under_mor Y Z -> Under_mor X Z.
  Proof.
    intros f g.
    exact (mk_Under_mor X Z (Under_mor_mor f · Under_mor_mor g) (Under_comp_eq f g)).
  Defined.

  Definition Undercategory_ob_mor : precategory_ob_mor.
  Proof.
    exists Under_ob.
    exact Under_mor.
  Defined.

  Definition Undercategory_data : precategory_data.
  Proof.
    exists Undercategory_ob_mor.
    split.
    - exact Under_id.
    - exact Under_comp.
  Defined.

  Definition is_precategory_Undercategory_data : is_precategory Undercategory_data.
  Proof.
    repeat split.
    - intros. apply Under_mor_equality. apply id_left.
    - intros. apply Under_mor_equality. apply id_right.
    - intros. apply Under_mor_equality. apply assoc.
    - intros. apply Under_mor_equality. apply assoc'.
  Defined.

  Definition Undercategory : precategory.
  Proof.
    exists Undercategory_data.
    exact is_precategory_Undercategory_data.
  Defined.

  Lemma has_homsets_Under : has_homsets Undercategory.
  Proof.
    intros X Y.
    apply (isaset_Under_mor X Y).
  Qed.

End def_underprecategories.


(** * Morphism of tips induces a functor *)
Section undercategories_morphisms.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Local Notation "c / C" := (@Undercategory C hs c).

  Definition Under_precategories_mor_ob {c c' : C} (h : C⟦c, c'⟧) : c' / C → c / C.
  Proof.
    intro af.
    exists (pr1 af).
    exact (h · pr2 af).
  Defined.

  Local Lemma Under_precategories_mor_mor_eq {c c' : C} (h : C⟦c, c'⟧)
             (af af' : c' / C) (g : (c' / C)⟦af, af'⟧) :
    (Under_ob_mor C c (Under_precategories_mor_ob h af)) · (Under_mor_mor C c' g) =
    (Under_ob_mor C c (Under_precategories_mor_ob h af')).
  Proof.
    cbn.
    rewrite <- assoc.
    apply cancel_precomposition.
    set (tmp := Under_mor_eq C c' g).
    unfold Under_mor_mor.
    unfold Under_mor_mor, Under_ob_mor in tmp.
    exact tmp.
  Qed.

  Definition Under_precategories_mor_mor {c c' : C} (h : C⟦c, c'⟧) (af af' : c' / C)
             (g : (c' / C)⟦af, af'⟧) : (c / C) ⟦Under_precategories_mor_ob h af,
                                                Under_precategories_mor_ob h af'⟧.
  Proof.
    exists (Under_mor_mor C c' g).
    exact (Under_precategories_mor_mor_eq h af af' g).
  Defined.

  Definition Under_precategories_mor_functor_data {c c' : C} (h : C⟦c, c'⟧) :
    functor_data (c' / C) (c / C).
  Proof.
    exists (Under_precategories_mor_ob h).
    exact (Under_precategories_mor_mor h).
  Defined.

  Lemma is_functor_Under_mor_functor_data {c c' : C} (h : C⟦c, c'⟧) :
    is_functor (Under_precategories_mor_functor_data h).
  Proof.
    split.
    - intro. apply (Under_mor_equality _ hs). apply idpath.
    - intros ? ? ? ? ?. apply (Under_mor_equality _ hs). apply idpath.
  Defined.

  Definition functor_Under_precategories_mor {c c' : C} (h : C⟦c, c'⟧) :
    functor _ _ := tpair _ _ (is_functor_Under_mor_functor_data h).

End undercategories_morphisms.
