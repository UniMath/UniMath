(** In this file, comonoids, commutative comonoids and comonoid homomorphisms are defined. **)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.

Local Open Scope cat.

Import MonoidalNotations.

Section ComonoidsAndMorphisms.

  Context {C : category} (M : monoidal C).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Definition comonoid_data (x : C) : UU
    := C⟦x, x ⊗ x⟧ × C⟦x, I⟧.

  Definition comonoid_data_comultiplication {x : C} (m : comonoid_data x)
    : C⟦x, x ⊗ x⟧
    := pr1 m.
  Notation "μ_{ m }" := (comonoid_data_comultiplication m).

  Definition comonoid_data_counit {x : C} (m : comonoid_data x)
    : C⟦x, I⟧
    := pr2 m.
  Notation "η_{ m }" := (comonoid_data_counit m).

  Definition comonoid_laws_assoc {x : C} (m : comonoid_data x) : UU
    := μ_{m} · (μ_{m} ⊗r x) · α x x x = μ_{m} · x ⊗l μ_{m}.

  Definition comonoid_laws_unit_left {x : C} (m : comonoid_data x) : UU
    := μ_{m} · (η_{m} ⊗r x) · lu x = identity x.
  Definition comonoid_laws_unit_right {x : C} (m : comonoid_data x) : UU
    := μ_{m} · (x ⊗l η_{m}) · ru x = identity x.

  Definition comonoid_laws {x : C} (m : comonoid_data x) : UU
    := comonoid_laws_unit_left m × comonoid_laws_unit_right m × comonoid_laws_assoc m.

  Lemma isaprop_comonoid_laws {x : C} (m : comonoid_data x)
    : isaprop (comonoid_laws m).
  Proof.
    repeat (apply isapropdirprod) ; apply homset_property.
  Qed.

  Definition comonoid (x : C) : UU
    := ∑ m : comonoid_data x, comonoid_laws m.

  Definition comonoid_to_comonoid_data {x : C} (m : comonoid x)
    : comonoid_data x := pr1 m.
  Coercion comonoid_to_comonoid_data : comonoid >-> comonoid_data.

  Definition comonoid_to_comonoid_laws {x : C} (m : comonoid x)
    : comonoid_laws m := pr2 m.

  Definition comonoid_to_unit_left_law {x : C} (m : comonoid x)
    : comonoid_laws_unit_left m := pr1 (comonoid_to_comonoid_laws m).

  Definition comonoid_to_unit_right_law {x : C} (m : comonoid x)
    : comonoid_laws_unit_right m := pr12 (comonoid_to_comonoid_laws m).

  Definition comonoid_to_assoc_law {x : C} (m : comonoid x)
    : comonoid_laws_assoc m := pr22 (comonoid_to_comonoid_laws m).

  Definition is_comonoid_mor_mult {x y : C}
             (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧) : UU
    := μ_{mx} · (f ⊗⊗ f) = f · μ_{my}.

  Definition is_comonoid_mor_unit {x y : C}
             (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧) : UU
    := f · η_{my} = η_{mx}.

  Definition is_comonoid_mor {x y : C}
             (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧) : UU
    := is_comonoid_mor_mult mx my f × is_comonoid_mor_unit mx my f.

  Lemma isaprop_is_comonoid_mor {x y : C}
        (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧)
    : isaprop (is_comonoid_mor mx my f).
  Proof.
    apply isapropdirprod ; apply homset_property.
  Qed.

  Lemma id_is_comonoid_mor {x : C} (xx : comonoid x)
    : is_comonoid_mor xx xx (identity x).
  Proof.
    split.
    - refine (_ @ ! id_left _).
      etrans. {
        apply maponpaths, bifunctor_distributes_over_id.
        apply (bifunctor_leftid M).
        apply (bifunctor_rightid M).
      }
      apply id_right.
    - apply id_left.
  Qed.

  Lemma comp_is_comonoid_mor {x y z : C}
        {f : C ⟦ x, y ⟧} {g : C ⟦ y, z ⟧}
        {xx : comonoid x} {yy : comonoid y} {zz : comonoid z}
        (pf : is_comonoid_mor xx yy f) (pg : is_comonoid_mor yy zz g)
    : is_comonoid_mor xx zz (f · g).
  Proof.
    split.
    - etrans. {
        apply maponpaths.
        apply bifunctor_distributes_over_comp.
        apply (bifunctor_leftcomp M).
        apply (bifunctor_rightcomp M).
        apply (bifunctor_equalwhiskers M).
      }
      etrans.
      { apply assoc. }
      etrans. {
        apply maponpaths_2.
        apply (pr1 pf).
      }
      etrans.
      { apply assoc'. }
      etrans. {
        apply maponpaths.
        apply (pr1 pg).
      }
      apply assoc.
    - unfold is_comonoid_mor_unit.
      etrans.
      { apply assoc'. }
      etrans. {
        apply maponpaths.
        apply (pr2 pg).
      }
      apply (pr2 pf).
  Qed.

End ComonoidsAndMorphisms.

Module ComonoidNotations.

  Notation "μ_{ m }" := (comonoid_data_comultiplication _ m).
  Notation "η_{ m }" := (comonoid_data_counit _ m).

End ComonoidNotations.

Section ComonoidAux.

  Context {C : category} (M : monoidal C).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Import ComonoidNotations.

  Definition comonoid_laws_assoc'
    {x : C} (m : comonoid M x)
    : μ_{m} · (μ_{m} ⊗r x) = μ_{m} · x ⊗l μ_{m} · αinv x x x.
  Proof.
    rewrite <- (comonoid_to_assoc_law M m).
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      exact (! pr1 (monoidal_associatorisolaw M x x x)).
    }
    now rewrite id_right.
  Qed.

  Definition comonoid_laws_unit_left'
    {x : C} (m : comonoid M x)
    : μ_{m} · (η_{m} ⊗r x) = luinv x.
  Proof.
    refine (_ @ id_left _).
    rewrite <- (comonoid_to_unit_left_law M m).
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      exact (! pr1 (monoidal_leftunitorisolaw M x)).
    }
    now rewrite id_right.
  Qed.

  Definition comonoid_laws_unit_right'
    {x : C} (m : comonoid M x)
    : μ_{m} · (x ⊗l η_{m})  = ruinv x.
  Proof.
    refine (_ @ id_left _).
    rewrite <- (comonoid_to_unit_right_law M m).
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      exact (! pr1 (monoidal_rightunitorisolaw M x)).
    }
    now rewrite id_right.
  Qed.

End ComonoidAux.

Section CommutativeComonoids.

  Context {C : category} {M : monoidal C} (S : symmetric M).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Let σ := pr1 S.

  Import ComonoidNotations.

  Definition is_commutative
    {x : C} (m : comonoid M x)
    : UU := μ_{m} · pr1 S x x = μ_{m}.

  Lemma comultiplication_comonoid_4times'
    {x : C} (m : comonoid M x)
    : μ_{m} · μ_{m} ⊗^{M} μ_{m}
      = μ_{m} · μ_{m} ⊗r x · α x x x · μ_{m} ⊗r _.
  Proof.
    etrans. {
      apply maponpaths.
      apply (bifunctor_equalwhiskers M).
    }

    unfold functoronmorphisms2.
    rewrite assoc.
    apply maponpaths_2.
    apply pathsinv0.
    apply comonoid_to_assoc_law.
  Qed.

  Lemma comultiplication_comonoid_4times_symmetry
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · μ_{m} ⊗^{M} μ_{m} · (pr1 S x x ⊗^{M} pr1 S x x)
      = μ_{m} · μ_{m} ⊗^{M} μ_{m}.
  Proof.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    now rewrite s.
  Qed.

  Lemma comultiplication_comonoid_4times_symmetry_left
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · μ_{m} ⊗^{M} μ_{m} · (pr1 S x x ⊗^{M}_{r} (x ⊗ x))
      = μ_{m} · μ_{m} ⊗^{M} μ_{m}.
  Proof.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- (when_bifunctor_becomes_rightwhiskering M).
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite id_right.
    now rewrite s.
  Qed.

  Lemma commutative_symmetric_braiding_using_lwhisker
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · μ_{m} ⊗^{M} μ_{m} · α^{M}_{_,_,_}
      = μ_{m} · (x ⊗l μ_{m}) · (x ⊗l (x ⊗l μ_{m})).
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      apply comonoid_to_assoc_law.
    }
    unfold functoronmorphisms1.
    rewrite ! assoc'.
    do 2 apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatornatleft M).
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · (x ⊗l μ_{m}) · (x ⊗l (x ⊗l μ_{m})) · x ⊗l αinv x x x
      = μ_{m} · (x ⊗l μ_{m}) · (x ⊗l (μ_{m} ⊗r x)).
  Proof.
    rewrite ! assoc'.
    rewrite <- ! (bifunctor_leftcomp M).
    do 2 apply maponpaths.
    refine (_ @ ! comonoid_laws_assoc' M m).
    apply assoc.
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker'
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · (x ⊗l μ_{m}) · (x ⊗l (μ_{m} ⊗r x)) · x ⊗l ((σ x x) ⊗r x)
      = μ_{m} · (x ⊗l μ_{m}) · (x ⊗l (μ_{m} ⊗r x)).
  Proof.
    rewrite ! assoc'.
    do 2 apply maponpaths.
    rewrite <- (bifunctor_leftcomp M).
    apply maponpaths.
    rewrite <- (bifunctor_rightcomp M).
    apply maponpaths.
    apply s.
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker''
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · μ_{m} ⊗^{M} μ_{m} · α^{M}_{_,_,_} · x ⊗l αinv x x x · x ⊗l ((σ x x) ⊗r x)
      = μ_{m} · (x ⊗l μ_{m}) · (x ⊗l (μ_{m} ⊗r x)).
  Proof.
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker' s).
    apply maponpaths_2.
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker s).
    apply maponpaths_2.
    exact (commutative_symmetric_braiding_using_lwhisker s).
  Qed.

  Lemma comultiplication_comonoid_4times
          {x : C} (m : comonoid M x) (s : is_commutative m)
    : μ_{ m} · x ⊗^{ M}_{l} μ_{ m} · x ⊗^{ M}_{l} (μ_{ m} ⊗^{ M}_{r} x)
      = μ_{ m} · μ_{ m} ⊗^{ M} μ_{ m} · α x x (x ⊗_{ M} x) · x ⊗^{ M}_{l} αinv x x x.
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact (! commutative_symmetric_braiding_using_lwhisker s).
    }

    rewrite ! assoc'.
    apply maponpaths.
    rewrite <- ! (bifunctor_leftcomp M).
    apply maponpaths.
    refine (comonoid_laws_assoc' M m @ _).
    apply assoc'.
  Qed.

  Lemma commutative_symmetric_braiding_after_4_copies'
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · μ_{m} ⊗^{M} μ_{m} · α^{M}_{_,_,_} · (x ⊗^{M}_{l} αinv^{M}_{_,_,_}) · (x ⊗^{M}_{l} (pr1 S x x ⊗^{M}_{r} x))
      = μ_{m} · μ_{m} ⊗^{M} μ_{m} · α^{M}_{_,_,_} · x ⊗^{M}_{l} αinv^{M}_{_,_,_}.
  Proof.
    refine (commutative_symmetric_braiding_using_lrwhisker'' s @ _).
    exact (comultiplication_comonoid_4times m s).
  Qed.

  Lemma commutative_symmetric_braiding_after_4_copies
    {x : C} {m : comonoid M x} (s : is_commutative m)
    : μ_{m} · (μ_{ m} ⊗^{ M} μ_{ m}
                 · (α^{ M }_{ x, x, x ⊗_{ M} x}
                         · (x ⊗^{ M}_{l} (αinv^{ M }_{ x, x, x} · (pr1 S x x ⊗^{ M}_{r} x · α^{ M }_{ x, x, x}))
                              · αinv^{ M }_{ x, x, x ⊗_{ M} x})))
      = μ_{m} · μ_{m} ⊗^{ M} μ_{m}.
  Proof.
    rewrite ! assoc.
    etrans. {
      apply maponpaths_2.
      rewrite ! (bifunctor_leftcomp M).
      rewrite ! assoc.
      apply maponpaths_2.
      exact (commutative_symmetric_braiding_after_4_copies' s).
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- (bifunctor_leftcomp M).
      rewrite (pr2 (monoidal_associatorisolaw M x x x)).
      apply (bifunctor_leftid M).
    }
    rewrite id_right.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      apply (pr1 (monoidal_associatorisolaw M x x _)).
    }
    apply id_right.
  Qed.

  Lemma comult_before_rearrange_and_swap
    {x y : C} (xx : comonoid M x) (yy : comonoid M y)
    : μ_{ xx} ⊗^{ M} μ_{ yy} · (rearrange_prod S x x y y · pr1 S x y ⊗^{ M} pr1 S x y)
      = μ_{ xx} ⊗^{ M} μ_{ yy} · (pr1 S (x ⊗_{ M} x) (y ⊗_{ M} y) · rearrange_prod S y y x x).
  Proof.
    apply maponpaths.
    apply rearrange_commute_with_swap.
  Qed.


End CommutativeComonoids.
