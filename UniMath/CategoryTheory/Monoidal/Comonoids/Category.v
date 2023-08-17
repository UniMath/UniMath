nner_swap
(**
nner_swap
In this file, the category of comonoids internal to a monoidal category is defined.
nner_swap
*)
nner_swap

nner_swap
Require Import UniMath.Foundations.All.
nner_swap
Require Import UniMath.MoreFoundations.All.
nner_swap
Require Import UniMath.CategoryTheory.Core.Categories.
nner_swap
Require Import UniMath.CategoryTheory.Core.Functors.
nner_swap
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Categories.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Functors.
nner_swap
Import BifunctorNotations.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Examples.DiagonalFunctor.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Examples.ConstantFunctor.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.categories.Dialgebras.
nner_swap

nner_swap
Local Open Scope cat.
nner_swap
Local Open Scope moncat.
nner_swap

nner_swap
Import MonoidalNotations.
nner_swap

nner_swap
Section CategoryOfComonoids.
nner_swap

nner_swap
  Context (V : monoidal_cat).
nner_swap

nner_swap
  Definition disp_cat_of_comonoids_data
nner_swap
    : disp_cat _
nner_swap
    := dirprod_disp_cat
nner_swap
         (dialgebra_disp_cat (functor_identity V) (diag_functor V))
nner_swap
         (dialgebra_disp_cat (functor_identity V) (constant_functor _ _ I_{V})).
nner_swap

nner_swap
  Definition comonoid_struct_data (x : V) : UU
nner_swap
    := disp_cat_of_comonoids_data x.
nner_swap

nner_swap
  Definition comonoid_data : UU
nner_swap
    := total_category disp_cat_of_comonoids_data.
nner_swap

nner_swap
  Definition comonoid_ob (m : comonoid_data)
nner_swap
    : ob V := pr1 m.
nner_swap
  Coercion comonoid_ob : comonoid_data >-> ob.
nner_swap

nner_swap
  Definition comonoid_comult (m : comonoid_data)
nner_swap
    : V⟦m , m ⊗ m⟧ := pr12 m.
nner_swap

nner_swap
  Notation "δ_{ m }" := (comonoid_comult m).
nner_swap

nner_swap
  Definition comonoid_counit (m : comonoid_data)
nner_swap
    : V⟦m , monoidal_unit V⟧ := pr22 m.
nner_swap

nner_swap
  Notation "ε_{ m }" := (comonoid_counit m).
nner_swap

nner_swap
  Definition comonoid_laws_assoc (m : comonoid_data) : UU
nner_swap
    := δ_{m} · (δ_{m} ⊗^{V}_{r} m) · mon_lassociator m m m = δ_{m} · m ⊗^{V}_{l} δ_{m}.
nner_swap

nner_swap
  Definition comonoid_laws_unit_left (m : comonoid_data) : UU
nner_swap
    := δ_{m} · (ε_{m} ⊗^{V}_{r} m) · mon_lunitor m = identity (comonoid_ob m).
nner_swap

nner_swap
  Definition comonoid_laws_unit_right (m : comonoid_data) : UU
nner_swap
    := δ_{m} · (m ⊗^{V}_{l} ε_{m}) · mon_runitor m = identity (comonoid_ob m).
nner_swap

nner_swap
  Definition comonoid_laws (m : comonoid_data)
nner_swap
    : UU
nner_swap
    := comonoid_laws_unit_left m × comonoid_laws_unit_right m × comonoid_laws_assoc m.
nner_swap

nner_swap
  Lemma isaprop_comonoid_laws (m : comonoid_data)
nner_swap
    : isaprop (comonoid_laws m).
nner_swap
  Proof.
nner_swap
    repeat (apply isapropdirprod) ; apply homset_property.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition comonoid_laws_disp_cat
nner_swap
    : disp_cat (total_category disp_cat_of_comonoids_data).
nner_swap
  Proof.
nner_swap
    exact (disp_full_sub _ (λ m, comonoid_laws m)).
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma locally_propositional_comonoid_laws_disp_cat
nner_swap
    : locally_propositional comonoid_laws_disp_cat.
nner_swap
  Proof.
nner_swap
    intro ; intros ; apply isapropunit.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition disp_cat_of_comonoids : disp_cat V
nner_swap
    := sigma_disp_cat comonoid_laws_disp_cat.
nner_swap

nner_swap
  Definition comonoid_struct (x : V) : UU
nner_swap
    := disp_cat_of_comonoids x.
nner_swap

nner_swap
  Definition comonoid_category : category
nner_swap
    := total_category disp_cat_of_comonoids.
nner_swap

nner_swap
  Definition comonoid : UU
nner_swap
    := total_category disp_cat_of_comonoids.
nner_swap

nner_swap
  Definition comonoid_to_struct (m : comonoid)
nner_swap
    : comonoid_struct (pr1 m)
nner_swap
    := pr12 m ,, pr22 m.
nner_swap

nner_swap
  Definition comonoid_to_data (m : comonoid)
nner_swap
    : comonoid_data
nner_swap
    := pr1 m ,, pr12 m.
nner_swap

nner_swap
  Coercion comonoid_to_data : comonoid >-> comonoid_data.
nner_swap

nner_swap
  Definition comonoid_to_law_assoc (m : comonoid)
nner_swap
    : comonoid_laws_assoc m := pr2 (pr222 m).
nner_swap

nner_swap
  Definition comonoid_to_law_unit_left (m : comonoid)
nner_swap
    : comonoid_laws_unit_left m := pr122 m.
nner_swap

nner_swap
  Definition comonoid_to_law_unit_right (m : comonoid)
nner_swap
    : comonoid_laws_unit_right m := pr1 (pr222 m).
nner_swap

nner_swap
  Definition comonoid_mor_struct (m n : comonoid) (f : V⟦m,n⟧): UU
nner_swap
    := (comonoid_to_struct m) -->[f] (comonoid_to_struct n).
nner_swap

nner_swap
  Definition make_is_comonoid_mor
nner_swap
    {m n : comonoid} {f : V⟦m,n⟧}
nner_swap
    (f_δ : δ_{m} · f #⊗ f = f · δ_{n})
nner_swap
    (f_ε : ε_{m} · identity I_{ V} = f · ε_{n})
nner_swap
    : comonoid_mor_struct m n f.
nner_swap
  Proof.
nner_swap
    simple refine ((_ ,, _) ,, _).
nner_swap
    - exact f_δ.
nner_swap
    - exact f_ε.
nner_swap
    - exact tt.
nner_swap
  Defined.
nner_swap

nner_swap
  Definition comonoid_mor (m n : comonoid)
nner_swap
    : UU
nner_swap
    := (total_category disp_cat_of_comonoids)⟦m,n⟧.
nner_swap

nner_swap
  Definition is_comonoid_mor_comult
nner_swap
    (m n : comonoid) (f : V⟦m,n⟧) : UU
nner_swap
    := δ_{m} · (f #⊗ f) = f · δ_{n}.
nner_swap

nner_swap
  Definition comonoid_mor_comult_law
nner_swap
    {m n : comonoid} (f : comonoid_mor m n)
nner_swap
    : is_comonoid_mor_comult m n (pr1 f)
nner_swap
    (* δ_{m} · (pr1 f ⊗⊗ pr1 f) = pr1 f · δ_{n} *)
nner_swap
    := pr112 f.
nner_swap

nner_swap
  Definition is_comonoid_mor_counit
nner_swap
    (m n : comonoid) (f : V⟦m,n⟧) : UU
nner_swap
    := f · ε_{n} = ε_{m}.
nner_swap

nner_swap
  Definition comonoid_mor_counit_law
nner_swap
    {m n : comonoid} (f : comonoid_mor m n)
nner_swap
    : is_comonoid_mor_counit m n (pr1 f)
nner_swap
    (* pr1 f · ε_{n} = ε_{m} *)
nner_swap
    := ! pr212 f @ id_right _.
nner_swap

nner_swap
  Lemma is_locally_propositional_comonoid
nner_swap
    : locally_propositional disp_cat_of_comonoids.
nner_swap
  Proof.
nner_swap
    intro ; intros.
nner_swap
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
nner_swap
    apply (isaprop_total2
nner_swap
             (_ ,, homset_property _ _ _ _ _)
nner_swap
             (λ _ , _ ,, homset_property _ _ _ _ _)).
nner_swap
  Qed.
nner_swap

nner_swap
End CategoryOfComonoids.
nner_swap

nner_swap
Module ComonoidNotations.
nner_swap

nner_swap
  Notation "δ_{ m }" := (comonoid_comult _ m).
nner_swap
  Notation "ε_{ m }" := (comonoid_counit _ m).
nner_swap

nner_swap
End ComonoidNotations.
nner_swap

nner_swap
Section CategoryOfCommutativeComonoids.
nner_swap

nner_swap
  Context (V : sym_monoidal_cat).
nner_swap

nner_swap
  Import ComonoidNotations.
nner_swap

nner_swap
  Definition is_commutative (m : comonoid V) : UU
nner_swap
    := δ_{m} · sym_mon_braiding V m m = δ_{m}.
nner_swap

nner_swap
  Definition commutative_comonoids_laws_disp_cat
nner_swap
    : disp_cat (comonoid_category V).
nner_swap
  Proof.
nner_swap
    exact (disp_full_sub _ is_commutative).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition disp_cat_of_commutative_comonoids
nner_swap
    := sigma_disp_cat commutative_comonoids_laws_disp_cat.
nner_swap

nner_swap
  Definition commutative_comonoid_category
nner_swap
    : category
nner_swap
    := total_category disp_cat_of_commutative_comonoids.
nner_swap

nner_swap
  Definition commutative_comonoid
nner_swap
    : UU
nner_swap
    := total_category disp_cat_of_commutative_comonoids.
nner_swap

nner_swap
  Definition commutative_comonoid_to_comonoid
nner_swap
    (m : commutative_comonoid) : comonoid V
nner_swap
    := pr1 m ,, pr12 m.
nner_swap

nner_swap
  Coercion commutative_comonoid_to_comonoid
nner_swap
    : commutative_comonoid >-> comonoid.
nner_swap

nner_swap
  Definition commutative_comonoid_is_commutative (m : commutative_comonoid)
nner_swap
    : is_commutative m
nner_swap
    := pr22 m.
nner_swap

nner_swap
  Lemma is_locally_propositional_commutative_comonoid
nner_swap
    : locally_propositional disp_cat_of_commutative_comonoids.
nner_swap
  Proof.
nner_swap
    intro ; intros.
nner_swap
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
nner_swap
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
nner_swap
    apply (isaprop_total2
nner_swap
             (_ ,, homset_property _ _ _ _ _)
nner_swap
             (λ _ , _ ,, homset_property _ _ _ _ _)).
nner_swap
  Qed.
nner_swap

nner_swap
End CategoryOfCommutativeComonoids.
nner_swap

nner_swap
Section ComonoidAux.
nner_swap

nner_swap
  Context (M : monoidal_cat).
nner_swap

nner_swap
  Import ComonoidNotations.
nner_swap

nner_swap
  Definition comonoid_laws_assoc'
nner_swap
    (m : comonoid M)
nner_swap
    : δ_{m} · (δ_{m} ⊗^{M}_{r} m) = δ_{m} · m ⊗^{M}_{l} δ_{m} · mon_rassociator m m m.
nner_swap
  Proof.
nner_swap
    rewrite <- comonoid_to_law_assoc.
nner_swap
    rewrite ! assoc'.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    now rewrite id_right.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition comonoid_laws_unit_left'
nner_swap
    (m : comonoid M)
nner_swap
    : δ_{m} · (ε_{m} ⊗^{M}_{r} m) = mon_linvunitor m.
nner_swap
  Proof.
nner_swap
    refine (_ @ id_left _).
nner_swap
    rewrite <- comonoid_to_law_unit_left.
nner_swap
    rewrite ! assoc'.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
    }
nner_swap
    now rewrite id_right.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition comonoid_laws_unit_right'
nner_swap
    (m : comonoid M)
nner_swap
    : δ_{m} · (m ⊗^{M}_{l} ε_{m})  = mon_rinvunitor m.
nner_swap
  Proof.
nner_swap
    refine (_ @ id_left _).
nner_swap
    rewrite <- (comonoid_to_law_unit_right M _).
nner_swap
    rewrite ! assoc'.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      apply monoidal_rightunitorisolaw.
nner_swap
    }
nner_swap
    now rewrite id_right.
nner_swap
  Qed.
nner_swap

nner_swap
End ComonoidAux.
nner_swap

nner_swap
Section CommutativeComonoids.
nner_swap

nner_swap
  Context (M : sym_monoidal_cat).
nner_swap
  Import ComonoidNotations.
nner_swap

nner_swap
  Lemma comultiplication_comonoid_4times'
nner_swap
    (m : comonoid M)
nner_swap
    : δ_{m} · δ_{m} #⊗ δ_{m}
nner_swap
      = δ_{m} · δ_{m} ⊗^{M}_{r} m · mon_lassociator _ _ _ · δ_{m}  ⊗^{M}_{r} _.
nner_swap
  Proof.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply (bifunctor_equalwhiskers M).
nner_swap
    }
nner_swap

nner_swap
    unfold functoronmorphisms2.
nner_swap
    rewrite assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    apply pathsinv0.
nner_swap
    apply comonoid_to_law_assoc.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comultiplication_comonoid_4times_symmetry
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · δ_{m} #⊗ δ_{m} · (sym_mon_braiding M m m #⊗ sym_mon_braiding M m m)
nner_swap
      = δ_{m} · δ_{m} #⊗ δ_{m}.
nner_swap
  Proof.
nner_swap
    rewrite assoc'.
nner_swap
    apply maponpaths.
nner_swap
    refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
    now rewrite commutative_comonoid_is_commutative.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comultiplication_comonoid_4times_symmetry_left
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · δ_{m} #⊗ δ_{m} · (sym_mon_braiding M m m ⊗^{M}_{r} (m ⊗_{M} m))
nner_swap
      = δ_{m} · δ_{m} #⊗ δ_{m}.
nner_swap
  Proof.
nner_swap
    rewrite assoc'.
nner_swap
    apply maponpaths.
nner_swap
    rewrite <- (when_bifunctor_becomes_rightwhiskering M).
nner_swap
    refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
    rewrite id_right.
nner_swap
    apply maponpaths_2.
nner_swap
    apply commutative_comonoid_is_commutative.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma commutative_symmetric_braiding_using_lwhisker
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_}
nner_swap
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (m ⊗^{M}_{l} δ_{m})).
nner_swap
  Proof.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      apply comonoid_to_law_assoc.
nner_swap
    }
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    apply pathsinv0.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply (monoidal_associatornatleft M).
nner_swap
    }
nner_swap
    now rewrite ! assoc.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma commutative_symmetric_braiding_using_lrwhisker
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (m ⊗^{M}_{l} δ_{m})) · m ⊗^{M}_{l} mon_rassociator _ _ _
nner_swap
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)).
nner_swap
  Proof.
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    rewrite <- (bifunctor_leftcomp M).
nner_swap
    etrans. {
nner_swap
      apply pathsinv0, (bifunctor_leftcomp M).
nner_swap
    }
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply (bifunctor_leftcomp M).
nner_swap
    }
nner_swap
    apply maponpaths.
nner_swap
    refine (_ @ ! comonoid_laws_assoc' M m).
nner_swap
    apply assoc.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma commutative_symmetric_braiding_using_lrwhisker'
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)) · m ⊗^{M}_{l} ((sym_mon_braiding M m m) ⊗^{M}_{r} m)
nner_swap
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)).
nner_swap
  Proof.
nner_swap
    rewrite ! assoc'.
nner_swap
    do 2 apply maponpaths.
nner_swap
    rewrite <- (bifunctor_leftcomp M).
nner_swap
    apply maponpaths.
nner_swap
    rewrite <- (bifunctor_rightcomp M).
nner_swap
    apply maponpaths.
nner_swap
    apply commutative_comonoid_is_commutative.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma commutative_symmetric_braiding_using_lrwhisker''
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_} · m ⊗^{M}_{l} mon_rassociator _ _ _ · m ⊗^{M}_{l} ((sym_mon_braiding M m m) ⊗^{M}_{r} m)
nner_swap
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)).
nner_swap
  Proof.
nner_swap
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker' _).
nner_swap
    apply maponpaths_2.
nner_swap
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker _).
nner_swap
    apply maponpaths_2.
nner_swap
    exact (commutative_symmetric_braiding_using_lwhisker _).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comultiplication_comonoid_4times
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · m ⊗^{M}_{l} δ_{ m} · m ⊗^{M}_{l} (δ_{ m} ⊗^{M}_{r} m)
nner_swap
      = δ_{m} · δ_{m} ⊗^{M} δ_{ m} · mon_lassociator _ _ (_ ⊗ m) · m ⊗^{M}_{l} mon_rassociator _ _ _.
nner_swap
  Proof.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      exact (! commutative_symmetric_braiding_using_lwhisker _).
nner_swap
    }
nner_swap

nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    rewrite <- (bifunctor_leftcomp M).
nner_swap
    etrans. {
nner_swap
      apply pathsinv0, (bifunctor_leftcomp M).
nner_swap
    }
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply (bifunctor_leftcomp M).
nner_swap
    }
nner_swap
    apply maponpaths.
nner_swap
    refine (comonoid_laws_assoc' M m @ _).
nner_swap
    apply assoc'.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma commutative_symmetric_braiding_after_4_copies'
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_} · (m ⊗^{M}_{l} αinv^{M}_{_,_,_}) · (m ⊗^{M}_{l} (sym_mon_braiding M m m ⊗^{M}_{r} m))
nner_swap
      = δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_} · m ⊗^{M}_{l} αinv^{M}_{_,_,_}.
nner_swap
  Proof.
nner_swap
    refine (commutative_symmetric_braiding_using_lrwhisker'' _ @ _).
nner_swap
    exact (comultiplication_comonoid_4times _).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma commutative_symmetric_braiding_after_4_copies
nner_swap
    (m : commutative_comonoid M)
nner_swap
    : δ_{m} · (δ_{m} #⊗ δ_{m}
nner_swap
                 · (α^{M}_{ m, m, m ⊗_{ M} m}
nner_swap
                         · (m ⊗^{M}_{l} (αinv^{M}_{ m, m, m} · (sym_mon_braiding M m m ⊗^{M}_{r} m · α^{M}_{ m, m, m}))
nner_swap
                              · αinv^{M}_{m, m, m ⊗_{ M} m})))
nner_swap
      = δ_{m} · δ_{m} #⊗ δ_{m}.
nner_swap
  Proof.
nner_swap
    rewrite ! assoc.
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      rewrite ! (bifunctor_leftcomp M).
nner_swap
      rewrite ! assoc.
nner_swap
      apply maponpaths_2.
nner_swap
      exact (commutative_symmetric_braiding_after_4_copies' _).
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      rewrite <- (bifunctor_leftcomp M).
nner_swap
      apply maponpaths.
nner_swap
      apply (monoidal_associatorisolaw M m m m).
nner_swap
    }
nner_swap
    rewrite (bifunctor_leftid M).
nner_swap
    rewrite id_right.
nner_swap

nner_swap
    etrans. {
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply (monoidal_associatorisolaw M m m _).
nner_swap
    }
nner_swap
    apply id_right.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comult_before_rearrange_and_swap
nner_swap
    (mx my : comonoid M)
nner_swap
    : δ_{mx} #⊗ δ_{my} · (rearrange_prod M _ _ _ _ · sym_mon_braiding M _ _ #⊗ sym_mon_braiding M _ _)
nner_swap
      = δ_{mx} #⊗ δ_{my} · (sym_mon_braiding M (_ ⊗ _) (_ ⊗ _) · rearrange_prod M _ _ _ _).
nner_swap
  Proof.
nner_swap
    apply maponpaths.
nner_swap
    apply rearrange_commute_with_swap.
nner_swap
  Qed.
nner_swap

nner_swap
End CommutativeComonoids.
nner_swap

nner_swap
Section Univalence.
nner_swap

nner_swap
  Lemma disp_cat_of_comonoids_is_univalent
nner_swap
    (V : monoidal_cat)
nner_swap
    : is_univalent_disp (disp_cat_of_comonoids V).
nner_swap
  Proof.
nner_swap
    apply is_univalent_sigma_disp.
nner_swap
    - apply dirprod_disp_cat_is_univalent
nner_swap
      ; apply is_univalent_dialgebra_disp_cat.
nner_swap
    - apply disp_full_sub_univalent.
nner_swap
      intro ; apply isaprop_comonoid_laws.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma disp_cat_of_commutative_comonoids_is_univalent
nner_swap
    (V : sym_monoidal_cat)
nner_swap
    : is_univalent_disp (disp_cat_of_commutative_comonoids V).
nner_swap
  Proof.
nner_swap
    apply is_univalent_sigma_disp.
nner_swap
    - apply disp_cat_of_comonoids_is_univalent.
nner_swap
    - apply disp_full_sub_univalent.
nner_swap
      intro ; apply homset_property.
nner_swap
  Qed.
nner_swap

nner_swap
End Univalence.
