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
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
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

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Section CategoryOfComonoids.

  Context (V : monoidal_cat).

  Definition disp_cat_of_comonoids_data
    : disp_cat V
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
    : V⟦m , monoidal_unit V⟧ := pr22 m.

  Notation "ε_{ m }" := (comonoid_counit m).

  Definition comonoid_laws_assoc (m : comonoid_data) : UU
    := δ_{m} · (δ_{m} ⊗^{V}_{r} m) · mon_lassociator m m m = δ_{m} · m ⊗^{V}_{l} δ_{m}.

  Definition comonoid_laws_unit_left (m : comonoid_data) : UU
    := δ_{m} · (ε_{m} ⊗^{V}_{r} m) · mon_lunitor m = identity (comonoid_ob m).

  Definition comonoid_laws_unit_right (m : comonoid_data) : UU
    := δ_{m} · (m ⊗^{V}_{l} ε_{m}) · mon_runitor m = identity (comonoid_ob m).

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
    : comonoid_laws_assoc m := pr2 (pr222 m).

  Definition comonoid_to_law_unit_left (m : comonoid)
    : comonoid_laws_unit_left m := pr122 m.

  Definition comonoid_to_law_unit_right (m : comonoid)
    : comonoid_laws_unit_right m := pr1 (pr222 m).

  Definition comonoid_mor_struct (m n : comonoid) (f : V⟦m,n⟧): UU
    := (comonoid_to_struct m) -->[f] (comonoid_to_struct n).

  Definition make_is_comonoid_mor
    {m n : comonoid} {f : V⟦m,n⟧}
    (f_δ : δ_{m} · f #⊗ f = f · δ_{n})
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
    := δ_{m} · (f #⊗ f) = f · δ_{n}.

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

  Import ComonoidNotations.

  Definition is_commutative (m : comonoid V) : UU
    := δ_{m} · sym_mon_braiding V m m = δ_{m}.

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

  Definition underlying_commutative_comonoid
    : commutative_comonoid_category ⟶ V
    := pr1_category _.
End CategoryOfCommutativeComonoids.

Section CommutativeComonoidsMorBuilder.
  Import ComonoidNotations.

  Context {V : sym_monoidal_cat}
          (C₁ C₂ : commutative_comonoid V)
          (f : underlying_commutative_comonoid _ C₁ --> underlying_commutative_comonoid _ C₂)
          (fδ : δ_{C₁} · f #⊗ f = f · δ_{C₂})
          (fε : ε_{C₁} = f · ε_{C₂}).

  Definition make_commutative_comonoid_mor
    : C₁ --> C₂.
  Proof.
    refine (f ,, ((_ ,, _) ,, tt) ,, tt).
    - exact fδ.
    - abstract
        (cbn ;
         rewrite id_right ;
         exact fε).
  Defined.
End CommutativeComonoidsMorBuilder.

Definition underlying_comonoid_mor
           {V : sym_monoidal_cat}
           {C₁ C₂ : commutative_comonoid V}
           (f : C₁ --> C₂)
  : underlying_commutative_comonoid _ C₁ --> underlying_commutative_comonoid _ C₂
  := pr1 f.

Section CommutativeComonoidsMorProjections.
  Import ComonoidNotations.

  Context {V : sym_monoidal_cat}
          {C₁ C₂ : commutative_comonoid V}
          (f : C₁ --> C₂).

  Proposition underlying_comonoid_mor_comult
    : δ_{C₁} · underlying_comonoid_mor f #⊗ underlying_comonoid_mor f
      =
      underlying_comonoid_mor f · δ_{C₂}.
  Proof.
    exact (pr1 (pr112 f)).
  Qed.

  Proposition underlying_comonoid_mor_counit
    : ε_{C₁} = underlying_comonoid_mor f · ε_{C₂}.
  Proof.
    refine (_ @ pr2 (pr112 f)).
    exact (!(id_right _)).
  Qed.
End CommutativeComonoidsMorProjections.

(**
 This gives a more convenient builder for commutative comonoids for
 the bundled version. Note: only one identity law has to be proven
 *)
Section MakeCommutativeComonoid.
  Context {V : sym_monoidal_cat}
          (x : V)
          (δ : x --> x ⊗ x)
          (ε : x --> I_{V})
          (unit_left : δ · (ε #⊗ identity x) · mon_lunitor x = identity x)
          (assocδ : δ · (δ #⊗ identity x) · mon_lassociator x x x = δ · (identity x #⊗ δ))
          (comm : δ · sym_mon_braiding V x x = δ).

  Definition make_commutative_comonoid_data
    : comonoid_data V
    := x ,, δ ,, ε.

  Proposition make_commutative_comonoid_laws
    : comonoid_laws V make_commutative_comonoid_data.
  Proof.
    repeat split.
    - refine (_ @ unit_left) ; cbn.
      apply maponpaths_2.
      apply maponpaths.
      rewrite tensor_mor_right.
      apply idpath.
    - refine (_ @ unit_left) ; cbn.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (!(comm)).
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite sym_mon_braiding_lunitor.
      apply maponpaths_2.
      rewrite tensor_mor_left.
      apply idpath.
    - unfold comonoid_laws_assoc ; cbn.
      refine (_ @ assocδ @ _).
      + apply maponpaths_2.
        apply maponpaths.
        rewrite tensor_mor_right.
        apply idpath.
      + apply maponpaths.
        rewrite tensor_mor_left.
        apply idpath.
  Qed.

  Definition make_commutative_comonoid
    : commutative_comonoid V.
  Proof.
    simple refine (x ,, ((δ ,, ε) ,, _) ,, _) ; cbn.
    - exact make_commutative_comonoid_laws.
    - exact comm.
  Defined.
End MakeCommutativeComonoid.

Section ComonoidAux.

  Context (M : monoidal_cat).

  Import ComonoidNotations.

  Definition comonoid_laws_assoc'
    (m : comonoid M)
    : δ_{m} · (δ_{m} ⊗^{M}_{r} m) = δ_{m} · m ⊗^{M}_{l} δ_{m} · mon_rassociator m m m.
  Proof.
    rewrite <- comonoid_to_law_assoc.
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      apply pathsinv0.
      apply monoidal_associatorisolaw.
    }
    now rewrite id_right.
  Qed.

  Definition comonoid_laws_unit_left'
    (m : comonoid M)
    : δ_{m} · (ε_{m} ⊗^{M}_{r} m) = mon_linvunitor m.
  Proof.
    refine (_ @ id_left _).
    rewrite <- comonoid_to_law_unit_left.
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      apply pathsinv0.
      apply monoidal_leftunitorisolaw.
    }
    now rewrite id_right.
  Qed.

  Definition comonoid_laws_unit_right'
    (m : comonoid M)
    : δ_{m} · (m ⊗^{M}_{l} ε_{m})  = mon_rinvunitor m.
  Proof.
    refine (_ @ id_left _).
    rewrite <- (comonoid_to_law_unit_right M _).
    rewrite ! assoc'.
    etrans.
    2: {
      do 2 apply maponpaths.
      apply pathsinv0.
      apply monoidal_rightunitorisolaw.
    }
    now rewrite id_right.
  Qed.

End ComonoidAux.

Section CommutativeComonoids.

  Context (M : sym_monoidal_cat).
  Import ComonoidNotations.

  Lemma comultiplication_comonoid_4times'
    (m : comonoid M)
    : δ_{m} · δ_{m} #⊗ δ_{m}
      = δ_{m} · δ_{m} ⊗^{M}_{r} m · mon_lassociator _ _ _ · δ_{m}  ⊗^{M}_{r} _.
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
    : δ_{m} · δ_{m} #⊗ δ_{m} · (sym_mon_braiding M m m #⊗ sym_mon_braiding M m m)
      = δ_{m} · δ_{m} #⊗ δ_{m}.
  Proof.
    rewrite assoc'.
    apply maponpaths.
    refine (! tensor_comp_mor _ _ _ _ @ _).
    now rewrite commutative_comonoid_is_commutative.
  Qed.

  Lemma comultiplication_comonoid_4times_symmetry_left
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} #⊗ δ_{m} · (sym_mon_braiding M m m ⊗^{M}_{r} (m ⊗_{M} m))
      = δ_{m} · δ_{m} #⊗ δ_{m}.
  Proof.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- (when_bifunctor_becomes_rightwhiskering M).
    refine (! tensor_comp_mor _ _ _ _ @ _).
    rewrite id_right.
    apply maponpaths_2.
    apply commutative_comonoid_is_commutative.
  Qed.

  Lemma commutative_symmetric_braiding_using_lwhisker
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_}
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (m ⊗^{M}_{l} δ_{m})).
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      apply comonoid_to_law_assoc.
    }
    rewrite ! assoc'.
    apply maponpaths.
    apply pathsinv0.
    etrans. {
      apply maponpaths.
      apply (monoidal_associatornatleft M).
    }
    now rewrite ! assoc.
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker
    (m : commutative_comonoid M)
    : δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (m ⊗^{M}_{l} δ_{m})) · m ⊗^{M}_{l} mon_rassociator _ _ _
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)).
  Proof.
    rewrite ! assoc'.
    apply maponpaths.
    rewrite <- (bifunctor_leftcomp M).
    etrans. {
      apply pathsinv0, (bifunctor_leftcomp M).
    }
    etrans.
    2: {
      apply (bifunctor_leftcomp M).
    }
    apply maponpaths.
    refine (_ @ ! comonoid_laws_assoc' M m).
    apply assoc.
  Qed.

  Lemma commutative_symmetric_braiding_using_lrwhisker'
    (m : commutative_comonoid M)
    : δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)) · m ⊗^{M}_{l} ((sym_mon_braiding M m m) ⊗^{M}_{r} m)
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)).
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
    : δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_} · m ⊗^{M}_{l} mon_rassociator _ _ _ · m ⊗^{M}_{l} ((sym_mon_braiding M m m) ⊗^{M}_{r} m)
      = δ_{m} · (m ⊗^{M}_{l} δ_{m}) · (m ⊗^{M}_{l} (δ_{m} ⊗^{M}_{r} m)).
  Proof.
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker' _).
    apply maponpaths_2.
    refine (_ @ commutative_symmetric_braiding_using_lrwhisker _).
    apply maponpaths_2.
    exact (commutative_symmetric_braiding_using_lwhisker _).
  Qed.

  Lemma comultiplication_comonoid_4times
    (m : commutative_comonoid M)
    : δ_{m} · m ⊗^{M}_{l} δ_{ m} · m ⊗^{M}_{l} (δ_{ m} ⊗^{M}_{r} m)
      = δ_{m} · δ_{m} ⊗^{M} δ_{ m} · mon_lassociator _ _ (_ ⊗ m) · m ⊗^{M}_{l} mon_rassociator _ _ _.
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact (! commutative_symmetric_braiding_using_lwhisker _).
    }

    rewrite ! assoc'.
    apply maponpaths.
    rewrite <- (bifunctor_leftcomp M).
    etrans. {
      apply pathsinv0, (bifunctor_leftcomp M).
    }
    etrans.
    2: {
      apply (bifunctor_leftcomp M).
    }
    apply maponpaths.
    refine (comonoid_laws_assoc' M m @ _).
    apply assoc'.
  Qed.

  Lemma commutative_symmetric_braiding_after_4_copies'
    (m : commutative_comonoid M)
    : δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_} · (m ⊗^{M}_{l} αinv^{M}_{_,_,_}) · (m ⊗^{M}_{l} (sym_mon_braiding M m m ⊗^{M}_{r} m))
      = δ_{m} · δ_{m} #⊗ δ_{m} · α^{M}_{_,_,_} · m ⊗^{M}_{l} αinv^{M}_{_,_,_}.
  Proof.
    refine (commutative_symmetric_braiding_using_lrwhisker'' _ @ _).
    exact (comultiplication_comonoid_4times _).
  Qed.

  Lemma commutative_symmetric_braiding_after_4_copies
    (m : commutative_comonoid M)
    : δ_{m} · (δ_{m} #⊗ δ_{m}
                 · (α^{M}_{ m, m, m ⊗_{ M} m}
                         · (m ⊗^{M}_{l} (αinv^{M}_{ m, m, m} · (sym_mon_braiding M m m ⊗^{M}_{r} m · α^{M}_{ m, m, m}))
                              · αinv^{M}_{m, m, m ⊗_{ M} m})))
      = δ_{m} · δ_{m} #⊗ δ_{m}.
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
      apply (monoidal_associatorisolaw M m m m).
    }
    rewrite (bifunctor_leftid M).
    rewrite id_right.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      apply (monoidal_associatorisolaw M m m _).
    }
    apply id_right.
  Qed.

  Lemma comult_before_inner_swap_and_swap
    (mx my : comonoid M)
    : δ_{mx} #⊗ δ_{my} · (inner_swap M _ _ _ _ · sym_mon_braiding M _ _ #⊗ sym_mon_braiding M _ _)
      = δ_{mx} #⊗ δ_{my} · (sym_mon_braiding M (_ ⊗ _) (_ ⊗ _) · inner_swap M _ _ _ _).
  Proof.
    apply maponpaths.
    apply inner_swap_commute_with_swap.
  Qed.

End CommutativeComonoids.

Section Univalence.

  Lemma disp_cat_of_comonoids_is_univalent
    (V : monoidal_cat)
    : is_univalent_disp (disp_cat_of_comonoids V).
  Proof.
    apply is_univalent_sigma_disp.
    - apply dirprod_disp_cat_is_univalent
      ; apply is_univalent_dialgebra_disp_cat.
    - apply disp_full_sub_univalent.
      intro ; apply isaprop_comonoid_laws.
  Qed.

  Lemma disp_cat_of_commutative_comonoids_is_univalent
    (V : sym_monoidal_cat)
    : is_univalent_disp (disp_cat_of_commutative_comonoids V).
  Proof.
    apply is_univalent_sigma_disp.
    - apply disp_cat_of_comonoids_is_univalent.
    - apply disp_full_sub_univalent.
      intro ; apply homset_property.
  Qed.

End Univalence.
