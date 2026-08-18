(** In this file, the category of monoids internal to a monoidal category is defined

Note: after refactoring on March 10, 2023, the prior Git history of this development is found via
git log -- UniMath/CategoryTheory/Monoidal/CategoriesOfMonoidsWhiskered.v
(git log -- UniMath/CategoryTheory/Monoidal/CategoriesOfMonoids.v gives information on a prior development for the "tensored" format of monoidal categories)

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

Section Category_of_Monoids.

  Context {C : category} (M : monoidal C).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.

  Definition monoid_data (x : C) : UU
    := C⟦x ⊗ x, x⟧ × C⟦I, x⟧.

  Definition monoid_data_multiplication {x : C} (m : monoid_data x)
    : C⟦x ⊗ x, x⟧
    := pr1 m.
  Notation "μ_{ m }" := (monoid_data_multiplication m).

  Definition monoid_data_unit {x : C} (m : monoid_data x)
    : C⟦I, x⟧
    := pr2 m.
  Notation "η_{ m }" := (monoid_data_unit m).

  Definition monoid_laws_assoc {x : C} (m : monoid_data x) : UU
    := α x x x · (x ⊗l μ_{m}) · μ_{m} = μ_{m} ⊗r x · μ_{m}.

  Definition monoid_laws_unit_left {x : C} (m : monoid_data x) : UU
    := (η_{m} ⊗r x) · μ_{m} = lu x.
  Definition monoid_laws_unit_right {x : C} (m : monoid_data x) : UU
    := (x ⊗l η_{m}) · μ_{m} = ru x.

  Definition monoid_laws {x : C} (m : monoid_data x) : UU
    := monoid_laws_unit_left m × monoid_laws_unit_right m × monoid_laws_assoc m.

  Lemma isaprop_monoid_laws {x : C} (m : monoid_data x)
    : isaprop (monoid_laws m).
  Proof.
    repeat (apply isapropdirprod) ; apply homset_property.
  Qed.

  Definition monoid (x : C) : UU
    := ∑ m : monoid_data x, monoid_laws m.

  Definition make_monoid
    {x : C} (μ : C⟦x ⊗ x, x⟧) (η : C⟦monoidal_unit M, x⟧)
    (p_ul : (η ⊗r x) · μ = lu x)
    (p_ur : (x ⊗l η) · μ = ru x)
    (p_assoc : α x x x · (x ⊗l μ) · μ = μ ⊗r x · μ)
    : monoid x.
  Proof.
    simple refine ((_ ,, _) ,, (_ ,, _ ,, _)).
    - exact μ.
    - exact η.
    - exact p_ul.
    - exact p_ur.
    - exact p_assoc.
  Defined.

  Definition monoid_to_monoid_data {x : C} (m : monoid x)
    : monoid_data x := pr1 m.
  Coercion monoid_to_monoid_data : monoid >-> monoid_data.

  Definition monoid_to_monoid_laws {x : C} (m : monoid x)
    : monoid_laws m := pr2 m.

  Definition monoid_to_unit_left_law {x : C} (m : monoid x)
    : monoid_laws_unit_left m := pr1 (monoid_to_monoid_laws m).

  Definition monoid_to_unit_right_law {x : C} (m : monoid x)
    : monoid_laws_unit_right m := pr12 (monoid_to_monoid_laws m).

  Definition monoid_to_assoc_law {x : C} (m : monoid x)
    : monoid_laws_assoc m := pr22 (monoid_to_monoid_laws m).

  Definition is_monoid_mor_mult {x y : C}
             (mx : monoid x) (my : monoid y) (f : C⟦x,y⟧) : UU
    := (f ⊗⊗ f) · μ_{my} = μ_{mx} · f.

  Definition is_monoid_mor_unit {x y : C}
             (mx : monoid x) (my : monoid y) (f : C⟦x,y⟧) : UU
    := η_{mx} · f = η_{my}.

  Definition is_monoid_mor {x y : C}
             (mx : monoid x) (my : monoid y) (f : C⟦x,y⟧) : UU
    := is_monoid_mor_mult mx my f × is_monoid_mor_unit mx my f.

  Lemma isaprop_is_monoid_mor {x y : C}
        (mx : monoid x) (my : monoid y) (f : C⟦x,y⟧)
    : isaprop (is_monoid_mor mx my f).
  Proof.
    apply isapropdirprod ; apply homset_property.
  Qed.

  Definition monoid_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    exists (λ x, monoid x).
    exact (λ x y mx my f, is_monoid_mor mx my f).
  Defined.

  Lemma id_is_monoid_mor {x : C} (xx : monoid x)
    : is_monoid_mor xx xx (identity x).
  Proof.
    split.
    - refine (_ @ ! id_right _).
      etrans. {
        apply maponpaths_2, bifunctor_distributes_over_id.
        apply (bifunctor_leftid M).
        apply (bifunctor_rightid M).
      }
      apply id_left.
    - apply id_right.
  Qed.

  Lemma comp_is_monoid_mor {x y z : C}
        {f : C ⟦ x, y ⟧} {g : C ⟦ y, z ⟧}
        {xx : monoid x} {yy : monoid y} {zz : monoid z}
        (pf : is_monoid_mor xx yy f) (pg : is_monoid_mor yy zz g)
    : is_monoid_mor xx zz (f · g).
  Proof.
    split.
    - etrans. {
        apply maponpaths_2.
        apply bifunctor_distributes_over_comp.
        apply (bifunctor_leftcomp M).
        apply (bifunctor_rightcomp M).
        apply (bifunctor_equalwhiskers M).
      }
      etrans.
      1: apply assoc'.
      etrans.
      1: apply maponpaths, (pr1 pg).
      etrans.
      1: apply assoc.
      etrans.
      1: apply maponpaths_2, (pr1 pf).
      apply assoc'.
    - unfold is_monoid_mor_unit.
      etrans.
      1: apply assoc.
      etrans.
      1: apply maponpaths_2, (pr2 pf).
      apply (pr2 pg).
  Qed.

  Definition monoid_disp_cat_id_comp
    : disp_cat_id_comp C monoid_disp_cat_ob_mor.
  Proof.
    split.
    - intro ; intro ; apply id_is_monoid_mor.
    - intros x y z f g xx yy zz pf pg.
      exact (comp_is_monoid_mor pf pg).
  Qed.

  Definition monoid_disp_cat_data : disp_cat_data C.
  Proof.
    exists monoid_disp_cat_ob_mor.
    exact monoid_disp_cat_id_comp.
  Defined.

  Lemma monoid_disp_cat_data_is_locally_propositional : locally_propositional monoid_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply isaprop_is_monoid_mor).
  Qed.

  Definition monoid_disp_cat : disp_cat C
    := make_disp_cat_locally_prop monoid_disp_cat_data_is_locally_propositional.

  Definition category_of_monoids_in_monoidal_cat : category
    := total_category monoid_disp_cat.

  Definition MON : category := category_of_monoids_in_monoidal_cat.

  Lemma MON_mor_eq {X X' : MON} (r r' : MON⟦X,X'⟧) : pr1 r = pr1 r' -> r = r'.
  Proof.
    apply mor_eq_total_category_when_locally_prop.
    exact monoid_disp_cat_data_is_locally_propositional.
  Qed.

  Definition monoid_carrier
             (X : MON)
    : ob C := pr1 X.

  Definition monoid_struct (X : MON)
    : monoid (monoid_carrier X)
    := pr2 X.

  Definition monoid_multiplication (X : MON)
    : C⟦monoid_carrier X ⊗_{ M} monoid_carrier X, monoid_carrier X⟧
    := monoid_data_multiplication (monoid_struct X).

  Definition monoid_unit (X : MON)
    : C⟦I, monoid_carrier X⟧
    := monoid_data_unit (monoid_struct X).

  Definition monoid_left_unit_law (X : MON)
    : monoid_laws_unit_left (monoid_struct X)
    := monoid_to_unit_left_law (monoid_struct X).

  Definition monoid_right_unit_law (X : MON)
    : monoid_laws_unit_right (monoid_struct X)
    := monoid_to_unit_right_law (monoid_struct X).

  Definition monoid_assoc_law (X : MON)
    : monoid_laws_assoc (monoid_struct X)
    := monoid_to_assoc_law (monoid_struct X).
End Category_of_Monoids.

Definition unit_monoid
  (V : monoidal_cat)
  : monoid V (monoidal_unit V).
Proof.
  use make_monoid.
  - exact (monoidal_leftunitordata V (monoidal_unit V)).
  - exact (identity (monoidal_unit V)).
  - etrans. {
      apply maponpaths_2.
      apply (bifunctor_rightid V).
    }
    apply id_left.
  - etrans. {
      apply maponpaths_2.
      apply (bifunctor_leftid V).
    }
    refine (id_left _ @ _).
    apply unitors_coincide_on_unit.
  - apply maponpaths_2.
    etrans.
    2: { rewrite unitors_coincide_on_unit.
         apply monoidal_triangleidentity. }
    apply idpath.
Defined.

(** Monoids in the monoidal category `monoidal_swapped M` and monoids in M are equivalent *)

Section MonoidsSwapped.
  Context {C : category} (M : monoidal C).

  Definition monoid_to_monoid_swapped_data {R : C} (m : monoid M R)
    : monoid_data (monoidal_swapped M) R.
  Proof.
    split; cbn.
    - exact (monoid_data_multiplication _ m).
    - exact (monoid_data_unit _ m).
  Defined.

  Lemma monoid_to_monoid_swapped_laws
    {R : C} (m : monoid M R)
    : monoid_laws (monoidal_swapped M) (monoid_to_monoid_swapped_data m).
  Proof.
    repeat split.
    - use monoid_to_unit_right_law.
    - use monoid_to_unit_left_law.
    - unfold monoid_laws_assoc; cbn.
      etrans.
      { rewrite <- assoc; refine (!maponpaths _ _); use monoid_to_assoc_law. }
      rewrite <- id_left; do 3 rewrite assoc.
      use (maponpaths (λ x, x · _ · _) (pr2 (monoidal_associatorisolaw _ _ _ _))).
  Qed.

  Definition monoid_to_monoid_swapped_monoid
    {R : C} (m : monoid M R)
    : monoid (monoidal_swapped M) R
    := monoid_to_monoid_swapped_data m ,, monoid_to_monoid_swapped_laws m.

  Definition monoid_to_monoid_swapped_mon (R : MON M)
    : MON (monoidal_swapped M)
    := pr1 R ,, monoid_to_monoid_swapped_monoid (pr2 R).

  Lemma monoid_to_monoid_swapped_mor_law {R R' : MON M} (f : R --> R')
    : is_monoid_mor (monoidal_swapped M) (monoid_to_monoid_swapped_monoid (pr2 R))
      (monoid_to_monoid_swapped_monoid (pr2 R')) (pr1 f).
  Proof.
    split.
    - unfold is_monoid_mor_mult.
      cbn; rewrite (monoidal_swapped_whiskering M).
      use (pr12 f).
    - use (pr22 f).
  Qed.

  Definition monoid_to_monoid_swapped_mor
    (R R' : MON M) (f : R --> R')
    : monoid_to_monoid_swapped_mon R --> monoid_to_monoid_swapped_mon R'
    := pr1 f ,, monoid_to_monoid_swapped_mor_law f.


  Definition monoid_to_monoid_swapped_functor_data
    : functor_data (MON M) (MON (monoidal_swapped M)).
  Proof.
    use tpair.
    - exact monoid_to_monoid_swapped_mon.
    - exact monoid_to_monoid_swapped_mor.
  Defined.

  Lemma monoid_to_monoid_swapped_functor_laws
    : is_functor monoid_to_monoid_swapped_functor_data.
  Proof.
    split.
    - intro.
      apply MON_mor_eq; easy.
    - intros ? ? ? ? ?.
      apply MON_mor_eq; easy.
  Qed.

  Definition monoid_to_monoid_swapped_functor : (MON M) ⟶ (MON (monoidal_swapped M))
    := make_functor monoid_to_monoid_swapped_functor_data monoid_to_monoid_swapped_functor_laws.

  Definition monoid_swapped_to_monoid_data {R : C} (m : monoid (monoidal_swapped M) R)
    : monoid_data M R.
  Proof.
    split; cbn.
    - exact (monoid_data_multiplication _ m).
    - exact (monoid_data_unit _ m).
  Defined.

  Lemma monoid_swapped_to_monoid_laws
    {R : C} (m : monoid (monoidal_swapped M) R)
    : monoid_laws M (monoid_swapped_to_monoid_data m).
  Proof.
    repeat split.
    - use (monoid_to_unit_right_law _ m).
    - use (monoid_to_unit_left_law _ m).
    - unfold monoid_laws_assoc; cbn.
      etrans.
      { rewrite <- assoc; refine (!maponpaths _ _); use (monoid_to_assoc_law _ m). }
      rewrite <- id_left; do 3 rewrite assoc.
      use (maponpaths (λ x, x · _ · _) (pr1 (monoidal_associatorisolaw _ _ _ _))).
  Qed.

  Definition monoid_swapped_to_monoid_monoid
    {R : C} (m : monoid (monoidal_swapped M) R)
    : monoid M R
    := monoid_swapped_to_monoid_data m ,, monoid_swapped_to_monoid_laws m.

  Definition monoid_swapped_to_monoid_mon (R : MON (monoidal_swapped M))
    : MON M
    := pr1 R ,, monoid_swapped_to_monoid_monoid (pr2 R).

  Lemma monoid_swapped_to_monoid_mor_law {R R' : MON (monoidal_swapped M)} (f : R --> R')
    : is_monoid_mor M (monoid_swapped_to_monoid_monoid (pr2 R))
      (monoid_swapped_to_monoid_monoid (pr2 R')) (pr1 f).
  Proof.
    split.
    - unfold is_monoid_mor_mult.
      cbn; rewrite (monoidal_swapped_whiskering (monoidal_swapped M)).
      use (pr12 f).
    - use (pr22 f).
  Qed.

  Definition monoid_swapped_to_monoid_mor
    (R R' : MON (monoidal_swapped M)) (f : R --> R')
    : monoid_swapped_to_monoid_mon R --> monoid_swapped_to_monoid_mon R'
    := pr1 f ,, monoid_swapped_to_monoid_mor_law f.


  Definition monoid_swapped_to_monoid_functor_data
    : functor_data (MON (monoidal_swapped M)) (MON M).
  Proof.
    use tpair.
    - exact monoid_swapped_to_monoid_mon.
    - exact monoid_swapped_to_monoid_mor.
  Defined.

  Lemma monoid_swapped_to_monoid_functor_laws
    : is_functor monoid_swapped_to_monoid_functor_data.
  Proof.
    split.
    - intro.
      apply MON_mor_eq; easy.
    - intros ? ? ? ? ?.
      apply MON_mor_eq; easy.
  Qed.

  Definition monoid_swapped_to_monoid_functor : (MON (monoidal_swapped M)) ⟶ (MON M)
    := make_functor monoid_swapped_to_monoid_functor_data monoid_swapped_to_monoid_functor_laws.

  Local Definition id_to_swap_unswap_data
    : nat_trans_data (functor_identity (MON M)) (monoid_to_monoid_swapped_functor ∙ monoid_swapped_to_monoid_functor).
  Proof.
    intro R; exists (identity _); cbn; split.
    - abstract (
        unfold is_monoid_mor_mult; cbn; unfold functoronmorphisms1;
        now rewrite (bifunctor_leftid M), (bifunctor_rightid M), id_left, id_left, id_right
      ).
    - abstract (use id_right).
  Defined.

  Local Lemma id_to_swap_unswap_nat
    : is_nat_trans _ _ id_to_swap_unswap_data.
  Proof.
    intros ? ? ?.
    apply MON_mor_eq.
    cbn; now rewrite id_left, id_right.
  Qed.

  Local Definition id_to_swap_unswap
    : functor_identity (MON M) ⟹ monoid_to_monoid_swapped_functor ∙ monoid_swapped_to_monoid_functor
    := make_nat_trans _ _ _ id_to_swap_unswap_nat.

  Local Definition unswap_swap_to_id_data
    : nat_trans_data (monoid_swapped_to_monoid_functor ∙ monoid_to_monoid_swapped_functor) (functor_identity (MON (monoidal_swapped M))).
  Proof.
    intro R; exists (identity _); cbn; split.
    - abstract (
        unfold is_monoid_mor_mult; cbn; unfold functoronmorphisms1;
        now rewrite (bifunctor_leftid (monoidal_swapped M)), (bifunctor_rightid (monoidal_swapped M)), id_left, id_left, id_right
      ).
    - abstract (use id_right).
  Defined.

  Local Definition unswap_swap_to_id_nat
    : is_nat_trans _ _ unswap_swap_to_id_data.
  Proof.
    intros ? ? ?.
    apply MON_mor_eq.
    cbn; now rewrite id_left, id_right.
  Defined.

  Local Definition unswap_swap_to_id
    : monoid_swapped_to_monoid_functor ∙ monoid_to_monoid_swapped_functor ⟹ functor_identity (MON (monoidal_swapped M))
    := make_nat_trans _ _ _ unswap_swap_to_id_nat.

  Definition equivalence_monoids_monoids_swapped_adjunction
    : adjunction_data (MON M) (MON (monoidal_swapped M)).
  Proof.
    use make_adjunction_data.
    - exact monoid_to_monoid_swapped_functor.
    - exact monoid_swapped_to_monoid_functor.
    - exact id_to_swap_unswap.
    - exact unswap_swap_to_id.
  Defined.

  Lemma equivalence_monoids_monoids_swapped_forms_equivalence
    : forms_equivalence equivalence_monoids_monoids_swapped_adjunction.
  Proof.
    split.
    - intro R; use tpair; cbn.
      + exists (identity _); split.
        * abstract (
            unfold is_monoid_mor_mult, functoronmorphisms1;
            now rewrite (bifunctor_leftid M), (bifunctor_rightid M), id_left, id_left, id_right
          ).
        * abstract (use id_right).
      + split.
        * apply MON_mor_eq.
          use id_left.
        * apply MON_mor_eq.
          use id_left.
    - intro R; use tpair; cbn.
      + exists (identity _); split.
        * abstract (
            unfold is_monoid_mor_mult, functoronmorphisms1;
            now rewrite (bifunctor_leftid (monoidal_swapped M)), (bifunctor_rightid (monoidal_swapped M)), id_left, id_left, id_right
          ).
        * abstract (use id_right).
      + split.
        * apply MON_mor_eq.
          use id_left.
        * apply MON_mor_eq.
          use id_left.
  Qed.

  Definition equivalence_monoids_monoids_swapped
    : equivalence_of_cats (MON M) (MON (monoidal_swapped M)).
  Proof.
    use make_equivalence_of_cats.
    - exact equivalence_monoids_monoids_swapped_adjunction.
    - exact equivalence_monoids_monoids_swapped_forms_equivalence.
  Defined.

End MonoidsSwapped.
