Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.


Local Open Scope cat.

Import Notations.

Section local_helper_lemmas.
  Lemma iso_stable_under_equality {C : category} {x y : C} {f g : C⟦x,y⟧} : (g = f) → (is_z_isomorphism f) → (is_z_isomorphism g).
  Proof.
    intros pe pi.
    induction pe.
    exact pi.
  Qed.

  Lemma iso_stable_under_transportf {C : category} {x y z : C} {f : C⟦x,y⟧} {pf : y=z} : (is_z_isomorphism f) → (is_z_isomorphism (transportf _ pf f)).
  Proof.
    intro pfi.
    induction pf.
    use pfi.
  Qed.

  Lemma iso_stable_under_equalitytransportf {C : category} {x y z : C} {f : C⟦x,y⟧} {g : C⟦x,z⟧} {pf : y=z} :
    (g = transportf _ pf f) -> (is_z_isomorphism f) -> (is_z_isomorphism g).
  Proof.
    intros p isof.
    use (iso_stable_under_equality p).
    use (iso_stable_under_transportf).
    exact isof.
  Qed.
End local_helper_lemmas.


Section MonoidalFunctors.

  Context (C D : category) (M : monoidalcategory C) (N : monoidalcategory D) (F : functor C D).

  Local Notation "F ·· G" := (functor_composite F G) (at level 31).
  Local Notation "α ··· β" := (nat_trans_comp _ _ _ α β) (at level 31).

  Local Notation "I_{ M }" := (unit_from_monoidalcatdata M).
  Local Notation "lu^{ M }_{ x }" := ( (leftunitor_from_monoidalcatdata M) x ).
  Local Notation "ru^{ M }_{ x }" := ( (rightunitor_from_monoidalcatdata M) x ).
  Local Notation "α^{ M }_{ x , y , z }" := (associatordata_from_monoidalcatdata M x y z).

  (** (Weak) Monoidal functors **)
  (* Monoidal functor data *)

  Definition functor_imageoftensor : bifunctor C C D
    := compose_bifunctor_with_functor M F.

  Definition functor_tensorofimages : bifunctor C C D
    := compose_functor_with_bifunctor F F N.

  Definition preserves_tensor : UU := binat_trans functor_tensorofimages functor_imageoftensor.
  Identity Coercion tensorpreservationintobinattrans: preserves_tensor >-> binat_trans.

  Definition preserves_unit : UU := D ⟦ I_{N} , F I_{M} ⟧.

  Definition monoidalfunctor_data :=
    preserves_tensor × preserves_unit.

  Definition tensorpreserved_from_monoidalfunctordata (mfd : monoidalfunctor_data) : preserves_tensor := pr1 mfd.
  Coercion tensorpreserved_from_monoidalfunctordata : monoidalfunctor_data >-> preserves_tensor.

  Definition unitpreserved_from_monoidalfunctordata (mfd : monoidalfunctor_data) : preserves_unit := pr2 mfd.
  Coercion unitpreserved_from_monoidalfunctordata : monoidalfunctor_data >-> preserves_unit.

  Definition preserves_leftunitality (pt : preserves_tensor) (pu : preserves_unit) :=
    ∏ (x : C), (pu ⊗^{ N}_{r} F x) · (pt I_{ M} x) · (# F lu^{ M }_{ x}) = lu^{ N }_{ F x}.

  Definition preserves_leftunitality' {pt : preserves_tensor} {pu : preserves_unit} (plu : preserves_leftunitality pt pu) :
    ∏ (x : C), (pu ⊗^{N} (identity (F x))) · (pt I_{M} x) · (#F (lu^{M}_{x})) = lu^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    rewrite bifunctor_leftid.
    rewrite id_right.
    apply plu.
  Qed.

  Definition preserves_rightunitality (pt : preserves_tensor) (pu : preserves_unit) :=
    ∏ (x : C), ((F x ⊗^{ N}_{l} pu) · (pt x I_{ M}) · (# F ru^{ M }_{ x}) = ru^{ N }_{ F x}).

  Definition preserves_rightunitality' {pt : preserves_tensor} {pu : preserves_unit} (pru : preserves_rightunitality pt pu) :
    ∏ (x : C), ((identity (F x)) ⊗^{N} pu) · (pt x I_{M}) · (#F (ru^{M}_{x})) = ru^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    rewrite bifunctor_rightid.
    rewrite id_left.
    apply pru.
  Qed.

  Definition preserves_associativity (pt : preserves_tensor) : UU :=
    ∏ (x y z : C), ((pt x y) ⊗^{N}_{r} (F z)) · (pt (x ⊗_{M} y) z) · (#F (α^{M}_{x,y,z}))
                   = α^{N}_{F x, F y, F z} · ((F x) ⊗^{N}_{l} (pt y z)) · (pt x (y ⊗_{M} z)).

  Definition monoidalfunctor_laws (mfd : monoidalfunctor_data) : UU :=
    (preserves_associativity mfd) × (preserves_leftunitality mfd mfd) × (preserves_rightunitality mfd mfd).

  Definition monoidalfunctor : UU :=
    ∑ (mfd : monoidalfunctor_data), monoidalfunctor_laws mfd.

  (** Strong and strict monoidal properties *)

  Definition preserves_tensor_strongly (pt : preserves_tensor) : UU :=
    is_binatiso pt.

  Definition preserves_tensor_strictly (pt : preserves_tensor) : UU :=
      ∏ (x y : C), ∑ (pf : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)),
      pt x y = transportf _ pf (identity ((F x) ⊗_{N} (F y))).

  Lemma strictlytensorpreserving_is_strong {pt : preserves_tensor} (pfstrict : preserves_tensor_strictly pt) : preserves_tensor_strongly pt.
  Proof.
    intros x y.
    use (iso_stable_under_equalitytransportf (pr2 (pfstrict x y)) (is_z_isomorphism_identity (F x ⊗_{N} F y))).
  Qed.
  Coercion strictlytensorpreserving_is_strong : preserves_tensor_strictly >-> preserves_tensor_strongly.

  Definition preserves_unit_strongly (pu : preserves_unit) : UU := is_z_isomorphism pu.

  Definition preserves_unit_strictly (pu : preserves_unit) : UU :=
    ∑ (pf : I_{N} = (F I_{M})), pu = transportf _ pf (identity I_{N}).

  Definition strictlyunitpreserving_is_strong {pu : preserves_unit} (pfstrict : preserves_unit_strictly pu) : preserves_unit_strongly pu.
  Proof.
    use (iso_stable_under_equalitytransportf (pr2 pfstrict) (is_z_isomorphism_identity I_{N})).
  Defined.
  Coercion strictlyunitpreserving_is_strong : preserves_unit_strictly >-> preserves_unit_strongly.

End MonoidalFunctors.
