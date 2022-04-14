Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.


Local Open Scope cat.

Section local_helper_lemmas.
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
End local_helper_lemmas.


Section Curried_Monoidal_Functors.

  Context (C D : category) (M : monoidalcategory_data C) (N : monoidalcategory_data D) (F : functor C D).

  Notation "x ⊗_{ M } y" := ((tensoronobjects_from_tensordata M) x y) (at level 31).
  Notation "f ⊗^{ M } g" := ((tensoronmorphisms_from_tensordata M) _ _ _ _ f g) (at level 31).
  Notation "I_{ M }" := (unit_from_monoidalcatdata M).
  Notation "lu^{ M }_{ x }" := (leftunitordata_from_monoidalcatdata M x ).
  Notation "ru^{ M }_{ x }" := (rightunitordata_from_monoidalcatdata M x ).
  Notation "α^{ M }_{ x , y , z }" := ((associatordata_from_monoidalcatdata M) x y z).

  (** (Weak) Monoidal functors **)
  (* Monoidal functor data *)
  Definition tensor_preserving_data : UU
    := ∏ (x y : C), D⟦(F x) ⊗_{N} (F y), F (x ⊗_{M} y)⟧.

  Definition unit_preserving_data : UU := D ⟦ I_{N} , F I_{M} ⟧.

  Definition monoidalfunctor_data :=
    tensor_preserving_data × unit_preserving_data.

  Definition tensorpreservingdata_from_monoidalfunctordata (mfd : monoidalfunctor_data) : tensor_preserving_data := pr1 mfd.
  Coercion tensorpreservingdata_from_monoidalfunctordata : monoidalfunctor_data >-> tensor_preserving_data.

  Definition unitpreservingdata_from_monoidalfunctordata (mfd : monoidalfunctor_data) : unit_preserving_data := pr2 mfd.
  Coercion unitpreservingdata_from_monoidalfunctordata : monoidalfunctor_data >-> unit_preserving_data.

  (* Weak monoidal functor properties *)
  Definition tensor_preserving_data_is_natural (tpd : tensor_preserving_data) :=
    ∏ (x y x' y' : C) (f : C⟦x,x'⟧) (g : C⟦y,y'⟧),
      (#F (f ⊗^{M} g))∘(tpd x y) = (tpd x' y')∘((#F f) ⊗^{N} (#F g)).

  Definition preserves_associativity (tpd : tensor_preserving_data) :=
    ∏ (x y z : C), (#F (α^{M}_{x,y,z})) ∘ (tpd (x ⊗_{M} y) z) ∘ ((tpd x y) ⊗^{N} (identity (F z)))
                   = (tpd x (y ⊗_{M} z)) ∘ ((identity (F x)) ⊗^{N} (tpd y z)) ∘ α^{N}_{F x, F y, F z}.

  Definition preserves_leftunitality (tpd : tensor_preserving_data) (upd : unit_preserving_data) : UU :=
    ∏ (x : C), ((#F (lu^{M}_{x})) ∘ (tpd I_{M} x) ∘ (upd ⊗^{N} (identity (F x)))) = lu^{N}_{F x}.

  Definition preserves_rightunitality (tpd : tensor_preserving_data) (upd : unit_preserving_data) : UU :=
    ∏ (x : C), (#F (ru^{M}_{x})) ∘ (tpd x I_{M}) ∘ ((identity (F x)) ⊗^{N} upd) = ru^{N}_{F x}.

  Definition monoidalfunctor_laws (mfd : monoidalfunctor_data) : UU :=
    (tensor_preserving_data_is_natural mfd) × (preserves_associativity mfd) ×
    (preserves_leftunitality mfd mfd) × (preserves_rightunitality mfd mfd).

  Definition monoidalfunctor : UU :=
    ∑ (mfd : monoidalfunctor_data), monoidalfunctor_laws mfd.


  (** Strong and strict monoidal properties *)

  Definition is_stronglytensorpreserving (tpd : tensor_preserving_data) : UU :=
    ∏ (x y : C), is_z_isomorphism (tpd x y).

  Definition is_strictlytensorpreserving (tpd : tensor_preserving_data) : UU :=
      ∏ (x y : C), ∑ (pf : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)),
      (tpd x y ) = transportf _ pf (identity ((F x) ⊗_{N} (F y))).

  Lemma strictlytensorpreserving_is_strong {tpd : tensor_preserving_data} (pfstrict : is_strictlytensorpreserving tpd) : is_stronglytensorpreserving tpd.
  Proof.
    intros x y.
    use (iso_stable_under_equalitytransportation (pr2 (pfstrict x y)) (is_z_isomorphism_identity ((F x) ⊗_{N} (F y)))).
  Defined.
  Coercion strictlytensorpreserving_is_strong : is_strictlytensorpreserving >-> is_stronglytensorpreserving.

  Definition is_stronglyunitpreserving (upd : unit_preserving_data) : UU := is_z_isomorphism upd.

  Definition is_strictlyunitpreserving (upd : unit_preserving_data) : UU :=
    ∑ (pf : I_{N} = (F I_{M})), upd = transportf _ pf (identity I_{N}).

  Definition strictlyunitpreserving_is_strong {upd : unit_preserving_data} (pfstrict : is_strictlyunitpreserving upd) : is_stronglyunitpreserving upd.
  Proof.
    use (iso_stable_under_equalitytransportation (pr2 pfstrict) (is_z_isomorphism_identity I_{N})).
  Defined.
  Coercion strictlyunitpreserving_is_strong : is_strictlyunitpreserving >-> is_stronglyunitpreserving.

End Curried_Monoidal_Functors.
