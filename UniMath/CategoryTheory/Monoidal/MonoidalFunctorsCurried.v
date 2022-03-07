Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.


Local Open Scope cat.

(* Remark: Here is a section because I introduce notation which is just used here *)
Section Curried_Monoidal_Functors.

  Notation "x ⊗_{ M } y" := (pr1 (tensor_extraction_of_monoidalcat M) x y) (at level 31).
  Notation "f ⊗^{ M } g" := (pr2 (tensor_extraction_of_monoidalcat M) _ _ _ _ f g) (at level 31).
  Notation "α^{ M }_{ x , y , z }" := (pr1 (associator_extraction_of_monoidalcat M) x y z).
  Notation "lu^{ M }_{ x }" := (pr1 (leftunitor_extraction_of_monoidalcat M) x ).
  Notation "ru^{ M }_{ x }" := (pr1 (rightunitor_extraction_of_monoidalcat M) x ) .
  Notation "I_{ M }" := (unit_extraction_of_monoidalcat M).

  Definition weakly_tensor_preserving_morphism {M N : monoidal_category} (F : functor M N) : UU
    := ∏ (x y : M), N⟦(F x) ⊗_{N} (F y), F (x ⊗_{M} y)⟧.

  Definition strongly_tensor_preserving_morphism {M N : monoidal_category} (F : functor M N) : UU :=
    ∑ (wtpm : weakly_tensor_preserving_morphism F), ∏ (x y : M), is_z_isomorphism (wtpm x y).

  Definition strongly_tensor_preserving_is_wtp {M N : monoidal_category} {F : functor M N} (stpm : strongly_tensor_preserving_morphism F) : (weakly_tensor_preserving_morphism F) : UU := pr1 stpm.
  Coercion strongly_tensor_preserving_is_wtp : strongly_tensor_preserving_morphism >-> weakly_tensor_preserving_morphism.

  Definition strictly_tensor_preserving_morphism {M N : monoidal_category} (F : functor M N) : UU :=
      ∑ (wtpm : weakly_tensor_preserving_morphism F), ∏ (x y : M), ∑ (pf : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)),
      (wtpm x y ) = transportf _ pf (identity ((F x) ⊗_{N} (F y))).

  (* I would assume that the following lemmas should already exists in the "iso file", but I can't find it (I need is_iso_stable_undertransportation)  *)
  Lemma iso_stable_under_equality {C : category} {x y : C} {f g : C⟦x,y⟧} : (g = f) → (is_z_isomorphism f) → (is_z_isomorphism g).
  Proof.
    intros pe pi.
    induction pe.
    exact pi.
  Qed.

  Lemma iso_stable_under_tranportation {C : category} {x y z : C} {f : C⟦x,y⟧} {pf : y=z} : (is_z_isomorphism f) → (is_z_isomorphism (transportf _ pf f)).
  Proof.
    intro pfi.
    induction pf.
    use pfi.
  Qed.

  Lemma iso_stable_under_equalitytransportation {C : category} {x y z : C} {f : C⟦x,y⟧} {g : C⟦x,z⟧} {pf : y=z} :
    (g = transportf _ pf f) -> (is_z_isomorphism f) -> (is_z_isomorphism g).
  Proof.
    intros p isof.
    use (iso_stable_under_equality p).
    use (iso_stable_under_tranportation).
    exact isof.
  Qed.


  Definition strictly_tensor_preserving_is_stp {M N : monoidal_category} {F : functor M N} (stpm : strictly_tensor_preserving_morphism F) : strongly_tensor_preserving_morphism F.
  Proof.
    split with (pr1 stpm).
    intros x y.
    set (pfequ := (pr2 (pr2 stpm x y))).
    set (idisiso := is_z_isomorphism_identity ((F x) ⊗_{N} (F y))).
    use (iso_stable_under_equalitytransportation pfequ idisiso).
 Defined.
  Coercion strictly_tensor_preserving_is_stp : strictly_tensor_preserving_morphism >-> strongly_tensor_preserving_morphism.

  Definition weakly_unit_preserving_morphism {M N : monoidal_category} (F : functor M N) := N ⟦ I_{N} , F I_{M} ⟧.
  Definition strongly_unit_preserving_morphism {M N : monoidal_category} (F : functor M N) :=
    ∑ (wupm : weakly_unit_preserving_morphism F), is_z_isomorphism wupm.

  Definition strongly_unit_preserving_is_wup {M N : monoidal_category} {F : functor M N} (supm : strongly_unit_preserving_morphism F) : weakly_unit_preserving_morphism F := pr1 supm.
  Coercion strongly_unit_preserving_is_wup : strongly_unit_preserving_morphism >-> weakly_unit_preserving_morphism.

  Definition strictly_unit_preserving_morphism {M N : monoidal_category} (F : functor M N) :=
    ∑ (wupm : weakly_unit_preserving_morphism F), ∑ (pf : I_{N} = (F I_{M})), wupm = transportf _ pf (identity I_{N}).

  Definition strictly_unit_preserving_is_sup {M N : monoidal_category} {F : functor M N} (supm : strictly_unit_preserving_morphism F) : strongly_unit_preserving_morphism F.
  Proof.
    split with (pr1 supm).
    set (pfequ := (pr2 (pr2 supm))).
    set (idisiso := is_z_isomorphism_identity I_{N}).
    use (iso_stable_under_equalitytransportation pfequ idisiso).
 Defined.
  Coercion strictly_unit_preserving_is_sup : strictly_unit_preserving_morphism >-> strongly_unit_preserving_morphism.


  Definition preserves_associativity {M N : monoidal_category} {F : functor M N} (wtpm : weakly_tensor_preserving_morphism F) :=
    ∏ (x y z : M), (#F (α^{M}_{x,y,z})) ∘ (wtpm (x ⊗_{M} y) z) ∘ ((wtpm x y) ⊗^{N} (identity (F z)))
                   = (wtpm x (y ⊗_{M} z)) ∘ ((identity (F x)) ⊗^{N} (wtpm y z)) ∘ α^{N}_{F x, F y, F z}.

  Definition preserves_leftunitality {M N : monoidal_category} {F : functor M N} (wtpm : weakly_tensor_preserving_morphism F) (wupm : weakly_unit_preserving_morphism F) : UU :=
    ∏ (x : M), ((#F (lu^{M}_{x})) ∘ (wtpm I_{M} x) ∘ (wupm ⊗^{N} (identity (F x)))) = lu^{N}_{F x}.

  Definition preserves_rightunitality {M N : monoidal_category} {F : functor M N} (wtpm : weakly_tensor_preserving_morphism F) (wupm : weakly_unit_preserving_morphism F) : UU :=
    ∏ (x : M), (#F (ru^{M}_{x})) ∘ (wtpm x I_{M}) ∘ ((identity (F x)) ⊗^{N} wupm) = ru^{N}_{F x}.

  Definition preserves_unitality {M N : monoidal_category} {F : functor M N} (wtpm : weakly_tensor_preserving_morphism F) (wupm : weakly_unit_preserving_morphism F) : UU :=
    (preserves_leftunitality wtpm wupm) × (preserves_rightunitality wtpm wupm).

  Definition weak_monoidal_functor (M N : monoidal_category) : UU :=
    ∑ (F : functor M N), ∑ (wtpm : weakly_tensor_preserving_morphism F), ∑ (wupm : weakly_unit_preserving_morphism F),
      (preserves_associativity wtpm) × (preserves_unitality wtpm wupm).

  Definition extract_underlyingfunctor {M N : monoidal_category} (F : weak_monoidal_functor M N) : (functor M N) := (pr1 F).
  Coercion extract_underlyingfunctor : weak_monoidal_functor >-> functor.

  Definition strong_monoidal_functor (M N : monoidal_category) : UU :=
    ∑ (F : functor M N), ∑ (stpm : strongly_tensor_preserving_morphism F), ∑ (supm : strongly_unit_preserving_morphism F),
      (preserves_associativity stpm) × (preserves_unitality stpm supm).

  Definition strict_monoidal_functor (M N : monoidal_category) :=
    ∑ (F : functor M N), ∑ (stpm : strictly_tensor_preserving_morphism F), ∑ (supm : strictly_unit_preserving_morphism F),
     (preserves_associativity stpm) × (preserves_unitality stpm supm).

  Lemma strict_monoidal_functor_is_strong_monoidal {M N : monoidal_category} (F : strict_monoidal_functor M N) :
    strong_monoidal_functor M N.
  Proof.
    split with (pr1 F).
    split with (pr1 (pr2 F)).
    split with (pr1 (pr2 (pr2 F))).
    use tpair.
    + use (pr1 (pr2 (pr2 (pr2 F)))).
    + use (pr2 (pr2 (pr2 (pr2 F)))).
  Defined.
  Coercion strict_monoidal_functor_is_strong_monoidal : strict_monoidal_functor >-> strong_monoidal_functor.

End Curried_Monoidal_Functors.
