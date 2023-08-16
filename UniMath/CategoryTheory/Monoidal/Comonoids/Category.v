(**
In this file, the category of comonoids internal to a monoidal category is defined.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
Require Import UniMath.CategoryTheory.Monoidal.Examples.DiagonalFunctor.
Require Import UniMath.CategoryTheory.Monoidal.Examples.ConstantFunctor.

Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.

Require Import UniMath.CategoryTheory.categories.Dialgebras.
(* Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalDialgebras. *)

Local Open Scope cat.

Import MonoidalNotations.

Section CategoryOfComonoids.

  Context (V : monoidal_cat).

  Notation "x ⊗ y" := (x ⊗_{V} y).
  Notation "x ⊗l f" := (x ⊗^{V}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{V}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{V} g) (at level 31).

  Let I : V := monoidal_unit V.
  Let lu : leftunitor_data V (monoidal_unit V) := monoidal_leftunitordata V.
  Let ru : rightunitor_data V (monoidal_unit V) := monoidal_rightunitordata V.
  Let α : associator_data V := monoidal_associatordata V.
  Let luinv : leftunitorinv_data V (monoidal_unit V) := monoidal_leftunitorinvdata V.
  Let ruinv : rightunitorinv_data V (monoidal_unit V) := monoidal_rightunitorinvdata V.
  Let αinv : associatorinv_data V := monoidal_associatorinvdata V.

  Definition disp_cat_of_comonoids_data
    : disp_cat _
    := dirprod_disp_cat
         (dialgebra_disp_cat (functor_identity V) (diag_functor V))
         (dialgebra_disp_cat (functor_identity V) (constant_functor _ _ I_{V})).

  Definition comonoid_struct_data (x : V) : UU
    := disp_cat_of_comonoids_data x.

  Definition comonoid_data : UU
    := total_category disp_cat_of_comonoids_data.

  Definition comonoid_ob (m : comonoid_data)
    : ob V := pr1 m.
  Coercion comonoid_ob : comonoid_data >-> ob.

  Definition comonoid_comult (m : comonoid_data)
    : V⟦m , m ⊗ m⟧ := pr12 m.

  Notation "δ_{ m }" := (comonoid_comult m).

  Definition comonoid_counit (m : comonoid_data)
    : V⟦m , I⟧ := pr22 m.

  Notation "ε_{ m }" := (comonoid_counit m).

  Definition comonoid_laws_assoc (m : comonoid_data) : UU
    := δ_{m} · (δ_{m} ⊗r m) · α m m m = δ_{m} · m ⊗l δ_{m}.

  Definition comonoid_laws_unit_left (m : comonoid_data) : UU
    := δ_{m} · (ε_{m} ⊗r m) · lu m = identity (comonoid_ob m).

  Definition comonoid_laws_unit_right (m : comonoid_data) : UU
    := δ_{m} · (m ⊗l ε_{m}) · ru m = identity (comonoid_ob m).

  Definition comonoid_laws (m : comonoid_data)
    : UU
    := comonoid_laws_unit_left m × comonoid_laws_unit_right m × comonoid_laws_assoc m.

  Lemma isaprop_comonoid_laws (m : comonoid_data)
    : isaprop (comonoid_laws m).
  Proof.
    repeat (apply isapropdirprod) ; apply homset_property.
  Qed.

  Definition comonoid_laws_disp_cat
    : disp_cat (total_category disp_cat_of_comonoids_data).
  Proof.
    exact (disp_full_sub _ (λ m, comonoid_laws m)).
  Defined.

  Lemma locally_propositional_comonoid_laws_disp_cat
    : locally_propositional comonoid_laws_disp_cat.
  Proof.
    intro ; intros ; apply isapropunit.
  Qed.

  Definition disp_cat_of_comonoids : disp_cat V
    := sigma_disp_cat comonoid_laws_disp_cat.

  Definition comonoid_struct (x : V) : UU
    := disp_cat_of_comonoids x.

  Definition comonoid_category : category
    := total_category disp_cat_of_comonoids.

  Definition comonoid : UU
    := total_category disp_cat_of_comonoids.

  Definition comonoid_to_struct (m : comonoid)
    : comonoid_struct (pr1 m)
    := pr12 m ,, pr22 m.

  Definition comonoid_to_data (m : comonoid)
    : comonoid_data
    := pr1 m ,, pr12 m.

  Coercion comonoid_to_data : comonoid >-> comonoid_data.

  Definition comonoid_to_law_assoc (m : comonoid)
    : comonoid_laws_assoc m.
  Proof.
    apply (pr2 m).
  Qed.

  Definition comonoid_to_law_unit_left (m : comonoid)
    : comonoid_laws_unit_left m.
  Proof.
    apply (pr2 m).
  Qed.

  Definition comonoid_to_law_unit_right (m : comonoid)
    : comonoid_laws_unit_right m.
  Proof.
    apply (pr2 m).
  Qed.

  Definition comonoid_mor_struct (m n : comonoid) (f : V⟦m,n⟧): UU
    := (comonoid_to_struct m) -->[f] (comonoid_to_struct n).

  Definition make_is_comonoid_mor
    {m n : comonoid} {f : V⟦m,n⟧}
    (f_δ : δ_{m} · f ⊗⊗ f = f · δ_{n})
    (f_ε : ε_{m} · identity I_{ V} = f · ε_{n})
    : comonoid_mor_struct m n f.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact f_δ.
    - exact f_ε.
    - exact tt.
  Defined.

  Definition comonoid_mor (m n : comonoid)
    : UU
    := (total_category disp_cat_of_comonoids)⟦m,n⟧.

  Definition is_comonoid_mor_comult
    (m n : comonoid) (f : V⟦m,n⟧) : UU
    := δ_{m} · (f ⊗⊗ f) = f · δ_{n}.

  Definition comonoid_mor_comult_law
    {m n : comonoid} (f : comonoid_mor m n)
    : is_comonoid_mor_comult m n (pr1 f)
    (* δ_{m} · (pr1 f ⊗⊗ pr1 f) = pr1 f · δ_{n} *)
    := pr112 f.

  Definition is_comonoid_mor_counit
    (m n : comonoid) (f : V⟦m,n⟧) : UU
    := f · ε_{n} = ε_{m}.

  Definition comonoid_mor_counit_law
    {m n : comonoid} (f : comonoid_mor m n)
    : is_comonoid_mor_counit m n (pr1 f)
    (* pr1 f · ε_{n} = ε_{m} *)
    := ! pr212 f @ id_right _.

  Lemma is_locally_propositional_comonoid
    : locally_propositional disp_cat_of_comonoids.
  Proof.
    intro ; intros.
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
    apply (isaprop_total2
             (_ ,, homset_property _ _ _ _ _)
             (λ _ , _ ,, homset_property _ _ _ _ _)).
  Qed.

End CategoryOfComonoids.

Module ComonoidNotations.

  Notation "δ_{ m }" := (comonoid_comult _ m).
  Notation "ε_{ m }" := (comonoid_counit _ m).

End ComonoidNotations.

Section CategoryOfCommutativeComonoids.

  Context (V : sym_monoidal_cat).

  Notation "x ⊗ y" := (x ⊗_{V} y).
  Notation "x ⊗l f" := (x ⊗^{V}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{V}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{V} g) (at level 31).

  Let I : V := monoidal_unit V.
  Let lu : leftunitor_data V (monoidal_unit V) := monoidal_leftunitordata V.
  Let ru : rightunitor_data V (monoidal_unit V) := monoidal_rightunitordata V.
  Let α : associator_data V := monoidal_associatordata V.
  Let luinv : leftunitorinv_data V (monoidal_unit V) := monoidal_leftunitorinvdata V.
  Let ruinv : rightunitorinv_data V (monoidal_unit V) := monoidal_rightunitorinvdata V.
  Let αinv : associatorinv_data V := monoidal_associatorinvdata V.
  Let σ := pr12 V.

  Import ComonoidNotations.

  Definition is_commutative (m : comonoid V) : UU
    := δ_{m} · σ m m = δ_{m}.

  Definition commutative_comonoids_laws_disp_cat
    : disp_cat (comonoid_category V).
  Proof.
    exact (disp_full_sub _ is_commutative).
  Defined.

  Definition disp_cat_of_commutative_comonoids
    := sigma_disp_cat commutative_comonoids_laws_disp_cat.

  Definition commutative_comonoid_category
    : category
    := total_category disp_cat_of_commutative_comonoids.

  Definition commutative_comonoid
    : UU
    := total_category disp_cat_of_commutative_comonoids.

  Definition commutative_comonoid_to_comonoid
    (m : commutative_comonoid) : comonoid V
    := pr1 m ,, pr12 m.

  Coercion commutative_comonoid_to_comonoid
    : commutative_comonoid >-> comonoid.

  Definition commutative_comonoid_is_commutative (m : commutative_comonoid)
    : is_commutative m
    := pr22 m.

  Lemma is_locally_propositional_commutative_comonoid
    : locally_propositional disp_cat_of_commutative_comonoids.
  Proof.
    intro ; intros.
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
    apply (isaprop_total2
             (_ ,, homset_property _ _ _ _ _)
             (λ _ , _ ,, homset_property _ _ _ _ _)).
  Qed.

End CategoryOfCommutativeComonoids.

Section ComonoidAux.

  Context (M : monoidal_cat).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : M := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Import ComonoidNotations.

  Definition comonoid_laws_assoc'
    (m : comonoid M)
    : δ_{m} · (δ_{m} ⊗r m) = δ_{m} · m ⊗l δ_{m} · αinv m m m.
  Proof.
    rewrite <- comonoid_to_law_assoc.
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      exact (! pr1 (monoidal_associatorisolaw M _ _ _)).
    }
    now rewrite id_right.
  Qed.

  Definition comonoid_laws_unit_left'
    (m : comonoid M)
    : δ_{m} · (ε_{m} ⊗r m) = luinv m.
  Proof.
    refine (_ @ id_left _).
    rewrite <- comonoid_to_law_unit_left.
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      exact (! pr1 (monoidal_leftunitorisolaw M _)).
    }
    now rewrite id_right.
  Qed.

  Definition comonoid_laws_unit_right'
    (m : comonoid M)
    : δ_{m} · (m ⊗l ε_{m})  = ruinv m.
  Proof.
    refine (_ @ id_left _).
    rewrite <- (comonoid_to_law_unit_right M _).
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      exact (! pr1 (monoidal_rightunitorisolaw M _)).
    }
    now rewrite id_right.
  Qed.

End ComonoidAux.

Section CommutativeComonoids.

  Context (M : sym_monoidal_cat).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : M := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.
  Let σ := pr12 M.

  Import ComonoidNotations.

  Lemma comultiplication_comonoid_4times'
    (m : comonoid M)
    : δ_{m} · δ_{m} ⊗^{M} δ_{m}
      = δ_{m} · δ_{m} ⊗r m · α _ _ _ · δ_{m} ⊗r _.
  Proof.
    etrans. {
      apply maponpaths.
      apply (bifunctor_equalwhiskers M).
    }

    unfold functoronmorphisms2.
    rewrite assoc.
    apply maponpaths_2.
    apply pathsinv0.
    apply comonoid_to_law_assoc.
  Qed.

  Lemma comultiplication_comonoid_4times_symmetry
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} ⊗^{M} δ_{m} · (σ m m ⊗^{M} σ m m)
      = δ_{m} · δ_{m} ⊗^{M} δ_{m}.
  Proof.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- (bifunctor_distributes_over_comp (F := M)); try (apply (pr21 M)).
    now rewrite commutative_comonoid_is_commutative.
  Qed.

  Lemma comultiplication_comonoid_4times_symmetry_left
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} ⊗^{M} δ_{m} · (σ m m ⊗^{M}_{r} (m ⊗ m))
      = δ_{m} · δ_{m} ⊗^{M} δ_{m}.
  Proof.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- (when_bifunctor_becomes_rightwhiskering M).
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
    rewrite id_right.
    now rewrite commutative_comonoid_is_commutative.
  Qed.

  Lemma commutative_symmetric_braiding_using_lwhisker
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} ⊗^{M} δ_{m} · α^{M}_{_,_,_}
      = δ_{m} · (m ⊗l δ_{m}) · (m ⊗l (m ⊗l δ_{m})).
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      apply comonoid_to_law_assoc.
    }
    unfold functoronmorphisms1.
    rewrite ! assoc'.
    do 2 apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatornatleft M).
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker
    (m : commutative_comonoid M)
    : δ_{m} · (m ⊗l δ_{m}) · (m ⊗l (m ⊗l δ_{m})) · m ⊗l αinv _ _ _
      = δ_{m} · (m ⊗l δ_{m}) · (m ⊗l (δ_{m} ⊗r m)).
  Proof.
    rewrite ! assoc'.
    rewrite <- ! (bifunctor_leftcomp M).
    do 2 apply maponpaths.
    refine (_ @ ! comonoid_laws_assoc' M m).
    apply assoc.
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker'
    (m : commutative_comonoid M)
    : δ_{m} · (m ⊗l δ_{m}) · (m ⊗l (δ_{m} ⊗r m)) · m ⊗l ((σ m m) ⊗r m)
      = δ_{m} · (m ⊗l δ_{m}) · (m ⊗l (δ_{m} ⊗r m)).
  Proof.
    rewrite ! assoc'.
    do 2 apply maponpaths.
    rewrite <- (bifunctor_leftcomp M).
    apply maponpaths.
    rewrite <- (bifunctor_rightcomp M).
    apply maponpaths.
    apply commutative_comonoid_is_commutative.
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker''
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} ⊗^{M} δ_{m} · α^{M}_{_,_,_} · m ⊗l αinv _ _ _ · m ⊗l ((σ m m) ⊗r m)
      = δ_{m} · (m ⊗l δ_{m}) · (m ⊗l (δ_{m} ⊗r m)).
  Proof.
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker' _).
    apply maponpaths_2.
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker _).
    apply maponpaths_2.
    exact (commutative_symmetric_braiding_using_lwhisker _).
  Qed.

  Lemma comultiplication_comonoid_4times
    (m : commutative_comonoid M)
    : δ_{ m} · m ⊗^{ M}_{l} δ_{ m} · m ⊗^{ M}_{l} (δ_{ m} ⊗^{ M}_{r} m)
      = δ_{ m} · δ_{ m} ⊗^{ M} δ_{ m} · α _ _ (_ ⊗_{ M} m) · m ⊗^{ M}_{l} αinv _ _ _.
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact (! commutative_symmetric_braiding_using_lwhisker _).
    }

    rewrite ! assoc'.
    apply maponpaths.
    rewrite <- ! (bifunctor_leftcomp M).
    apply maponpaths.
    refine (comonoid_laws_assoc' M m @ _).
    apply assoc'.
  Qed.

  Lemma commutative_symmetric_braiding_after_4_copies'
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} ⊗^{M} δ_{m} · α^{M}_{_,_,_} · (m ⊗^{M}_{l} αinv^{M}_{_,_,_}) · (m ⊗^{M}_{l} (σ m m ⊗^{M}_{r} m))
      = δ_{m} · δ_{m} ⊗^{M} δ_{m} · α^{M}_{_,_,_} · m ⊗^{M}_{l} αinv^{M}_{_,_,_}.
  Proof.
    refine (commutative_symmetric_braiding_using_lrwhisker'' _ @ _).
    exact (comultiplication_comonoid_4times _).
  Qed.

  Lemma commutative_symmetric_braiding_after_4_copies
    (m : commutative_comonoid M)
    : δ_{m} · (δ_{ m} ⊗^{ M} δ_{ m}
                 · (α^{ M }_{ m, m, m ⊗_{ M} m}
                         · (m ⊗^{ M}_{l} (αinv^{ M }_{ m, m, m} · (σ m m ⊗^{ M}_{r} m · α^{ M }_{ m, m, m}))
                              · αinv^{ M }_{ m, m, m ⊗_{ M} m})))
      = δ_{m} · δ_{m} ⊗^{ M} δ_{m}.
  Proof.
    rewrite ! assoc.
    etrans. {
      apply maponpaths_2.
      rewrite ! (bifunctor_leftcomp M).
      rewrite ! assoc.
      apply maponpaths_2.
      exact (commutative_symmetric_braiding_after_4_copies' _).
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- (bifunctor_leftcomp M).
      apply maponpaths.
      apply (pr2 (monoidal_associatorisolaw M m m m)).
    }
    rewrite (bifunctor_leftid M).
    rewrite id_right.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      apply (pr1 (monoidal_associatorisolaw M m m _)).
    }
    apply id_right.
  Qed.

  Lemma comult_before_rearrange_and_swap
    (mx my : comonoid M)
    : δ_{mx} ⊗^{ M} δ_{my} · (rearrange_prod (pr2 M) _ _ _ _ · σ _ _ ⊗^{ M} σ _ _)
      = δ_{mx} ⊗^{ M} δ_{my} · (σ (_ ⊗_{ M} _) (_ ⊗_{ M} _) · rearrange_prod (pr2 M) _ _ _ _).
  Proof.
    apply maponpaths.
    apply rearrange_commute_with_swap.
  Qed.

End CommutativeComonoids.
