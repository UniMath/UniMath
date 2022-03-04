Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.


Local Open Scope cat.

Section Curried_Monoidal_Functors.


  Notation "x ⊗_{ M } y" := (pr1 (tensor_extraction_of_monoidalcat M) x y) (at level 31).
  Notation "f ⊗^{ M } g" := (pr2 (tensor_extraction_of_monoidalcat M) _ _ _ _ f g) (at level 31).
  Notation "α^{ M }_{ x , y , z }" := (pr1 (associator_extraction_of_monoidalcat M) x y z).
  Notation "lu^{ M }_{ x }" := (pr1 (leftunitor_extraction_of_monoidalcat M) x ).
  Notation "ru^{ M }_{ x }" := (pr1 (rightunitor_extraction_of_monoidalcat M) x ) .
  Notation "I_{ M }" := (unit_extraction_of_monoidalcat M).

  (* Just here for notation testing *)
  Lemma testnotations (M : monoidal_category) (x x' y y' : M) (f : M⟦x,y⟧) (g : M⟦x',y'⟧) : nat.
  Proof.
    Check x⊗_{M}y.
    Check f⊗^{M}g.
    Check α^{M}_{x,y,x'}.
    Check lu^{M}_{x}.
    Check ru^{M}_{x}.
    Check I_{M}.
    exact (0).
  Qed.
  (* ---- *)

  Definition weakly_tensor_preserving_morphism {M N : monoidal_category} (F : functor M N) := ∏ (x y : M), N⟦(F x) ⊗_{N} (F y), F (x ⊗_{M} y)⟧.

  (*Definition strtenprm { M N} F := F(x ⊗ y ) = F(x) ⊗ F(y).
  Lemma getstricttensorprsmor (strtenprm)*)




  Definition strongly_tensor_preserving_morphism {M N : monoidal_category} (F : functor M N) :=
    ∑ (wtpm : weakly_tensor_preserving_morphism F), ∏ (x y : M), (is_z_isomorphism (wtpm x y)).

  Definition strongly_tensor_preserving_is_wtp {M N : monoidal_category} {F : functor M N} (stpm : strongly_tensor_preserving_morphism F) : (weakly_tensor_preserving_morphism F) := pr1 stpm.
  Coercion strongly_tensor_preserving_is_wtp : strongly_tensor_preserving_morphism >-> weakly_tensor_preserving_morphism.

  Definition strictly_tensor_preserving_morphism {M N : monoidal_category} (F : functor M N) :=
      ∑ (wtpm : weakly_tensor_preserving_morphism F), ∏ (x y : M), ∑ (pfx : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)),
      (wtpm x y ) = transportf _ pfx (identity ((F x) ⊗_{N} (F y))).

  Definition strictly_tensor_preserving_is_stp {M N : monoidal_category} {F : functor M N} (stpm : strictly_tensor_preserving_morphism F) : (strongly_tensor_preserving_morphism F).
  Proof.
    split with (pr1 stpm).
    intros x y.
    set (tpequ := (pr1 (pr2 stpm x y))).
    unfold is_z_isomorphism.
    set (idisiso := is_z_isomorphism_identity ((F x) ⊗_{N} (F y))).


Abort.

  (* Coercion strictly_tensor_preserving_is_stp : strictly_tensor_preserving_morphism >-> strongly_tensor_preserving_morphism. *)

  Definition preserves_associativity {M N : monoidal_category} {F : functor M N} (wtpm : weakly_tensor_preserving_morphism F) :=
    ∏ (x y z : M), (#F (α^{M}_{x,y,z})) ∘ (wtpm (x ⊗_{M} y) z) ∘ ((wtpm x y) ⊗^{N} (identity (F z)))
          = (wtpm x (y ⊗_{M} z)) ∘ ((identity (F x)) ⊗^{N} (wtpm y z)) ∘ (α^{N}_{F x, F y, F z}).

  Definition weakly_unit_preserving_morphism {M N : monoidal_category} (F : functor M N) := N ⟦ I_{N} , F I_{M} ⟧.
  Definition strongly_unit_preserving_morphism {M N : monoidal_category} (F : functor M N) :=
    ∑ (wupm : weakly_unit_preserving_morphism F), (is_iso wupm).

  Definition preserves_unitality {M N : monoidal_category} {F : functor M N} (wtpm : weakly_tensor_preserving_morphism F) (wupm : weakly_unit_preserving_morphism F) :=
    ∏ (x : M), (#F (ru^{M}_{x})) ∘ (wtpm x I_{M}) ∘ ((identity (F x)) ⊗^{N} wupm) = ru^{N}_{F x}.

  Definition strongly_unit_preserving_is_wup {M N : monoidal_category} {F : functor M N} (supm : strongly_unit_preserving_morphism F) : (weakly_unit_preserving_morphism F) := pr1 supm.
  Coercion strongly_unit_preserving_is_wup : strongly_unit_preserving_morphism >-> weakly_unit_preserving_morphism.



  Definition weak_monoidal_functor (M N : monoidal_category) :=
    ∑ (F : functor M N), ∑ (wtpm : weakly_tensor_preserving_morphism F), ∑ (wupm : weakly_unit_preserving_morphism F),
      (preserves_associativity wtpm) × (preserves_unitality wtpm wupm).

  Definition extract_underlyingfunctor {M N : monoidal_category} (F : weak_monoidal_functor M N) : (functor M N) := (pr1 F).
  Coercion extract_underlyingfunctor : weak_monoidal_functor >-> functor.

  Definition strong_monoidal_functor (M N : monoidal_category) :=
    ∑ (F : functor M N), ∑ (stpm : strongly_tensor_preserving_morphism F), ∑ (supm : strongly_unit_preserving_morphism F),
      (preserves_associativity stpm) × (preserves_unitality stpm supm).

  Definition strict_monoidal_functor (M N : monoidal_category) :=
    ∑ (F : functor M N), (strictly_tensor_preserving_morphism F). (* × strictly_unital_preserving_morphism F) *)

End Curried_Monoidal_Functors.
