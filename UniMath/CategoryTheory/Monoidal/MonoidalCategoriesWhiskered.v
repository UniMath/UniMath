Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Local Open Scope cat.

Import BifunctorNotations.

(** Data **)
Definition tensor (C : category) : UU :=
  bifunctor C C C.
Identity Coercion tensorintobifunctor : tensor >-> bifunctor.

Definition associator_data {C : category} (T : tensor C) : UU :=
  ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

Definition leftunitor_data {C : category} (T : tensor C) (I : C) : UU :=
  ∏ (x : C), C⟦I ⊗_{T} x, x⟧.

Definition nattransdata_from_leftunitordata {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I):
  nat_trans_data (leftwhiskering_functor T (bifunctor_leftid T) (bifunctor_leftcomp T) I) (functor_identity C).
Proof.
  exact (λ x, lu x).
Defined.

Definition rightunitor_data {C : category} (T : tensor C) (I : C) : UU :=
  ∏ (x : C), C⟦x ⊗_{T} I, x⟧.

Definition nattransdata_from_rightunitordata {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) :
  nat_trans_data (rightwhiskering_functor T (bifunctor_rightid T) (bifunctor_rightcomp T) I) (functor_identity C).
Proof.
  exact (λ x, ru x).
Defined.

Definition monoidalcategory_data (C : category): UU :=
    ∑ T : tensor C, ∑ I : C,
        (leftunitor_data T I) × (rightunitor_data T I) × (associator_data T).

Definition make_monoidalcat_data {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) (ru : rightunitor_data T I) (α : associator_data T) : monoidalcategory_data C := (T,,I,,lu,,ru,,α).

Definition tensor_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : tensor C := (pr1 MD).
Coercion tensor_from_monoidalcatdata : monoidalcategory_data >-> tensor.

Definition unit_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : C := (pr1 (pr2 MD)).
Notation "I_{ MD }" := (unit_from_monoidalcatdata MD).

Definition leftunitordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : leftunitor_data MD I_{MD} := (pr1 (pr2 (pr2 MD))).
Notation "lu_{ MD }" := (leftunitordata_from_monoidalcatdata MD).

Definition rightunitordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : rightunitor_data MD I_{MD} := (pr1 (pr2 (pr2 (pr2 MD)))).
Notation "ru_{ MD }" := (rightunitordata_from_monoidalcatdata MD).

Definition associatordata_from_monoidalcatdata {C : category} (MD : monoidalcategory_data C) : associator_data MD := (pr2 (pr2 (pr2 (pr2 MD)))).
Notation "α_{ MD }" := (associatordata_from_monoidalcatdata MD).

(** Axioms **)
Definition tensor_assoc_nat_leftwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x y z z' : C) (h : C⟦z,z'⟧),
    (α x y z) · (x ⊗^{ T}_{l} (y ⊗^{ T}_{l} h)) = ((x ⊗_{ T} y) ⊗^{ T}_{l} h) · (α x y z').

Definition tensor_assoc_nat_rightwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x x' y z : C) (f : C⟦x,x'⟧),
    (α x y z) · (f ⊗^{ T}_{r} (y ⊗_{ T} z)) = ((f ⊗^{ T}_{r} y) ⊗^{ T}_{r} z) · (α x' y z).

Definition tensor_assoc_nat_leftrightwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x y y' z : C) (g : C⟦y,y'⟧),
       (α x y z) · (x ⊗^{ T}_{l} (g ⊗^{ T}_{r} z)) = ((x ⊗^{ T}_{l} g) ⊗^{ T}_{r} z) · (α x y' z).

Definition tensor_assoc_nat1 {C : category} {T : tensor C} {α : associator_data T} (αnl : tensor_assoc_nat_leftwhisker α) (αnr : tensor_assoc_nat_rightwhisker α) (αnlr : tensor_assoc_nat_leftrightwhisker α) {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
       (α x y z) · ((f ⊗^{ T}_{r} (y ⊗_{ T} z)) · (x' ⊗^{ T}_{l} ((g ⊗^{ T}_{r} z) · (y' ⊗^{ T}_{l} h)))) =
         (((f ⊗^{ T}_{r} y) · (x' ⊗^{ T}_{l} g))  ⊗^{ T}_{r} z) · ((x' ⊗_{ T} y') ⊗^{ T}_{l} h) · (α x' y' z').
Proof.
  rewrite assoc.
  rewrite αnr.
  rewrite assoc'.
  etrans. {
    apply cancel_precomposition.
    rewrite (bifunctor_leftcomp T).
    rewrite assoc.
    rewrite αnlr.
    apply idpath.
  }

  etrans. {
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply αnl.
  }
  rewrite assoc.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0.
  rewrite bifunctor_rightcomp.
  apply idpath.
Qed.

Lemma tensor_assoc_nat2 {C : category} {T : tensor C} {α : associator_data T} (αnl : tensor_assoc_nat_leftwhisker α) (αnr : tensor_assoc_nat_rightwhisker α) (αnlr : tensor_assoc_nat_leftrightwhisker α)
      {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
    (f ⊗^{T} (g ⊗^{T} h))∘(α x y z) = (α x' y' z')∘ ((f ⊗^{T} g) ⊗^{T} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (tensor_assoc_nat1 αnl αnr αnlr f g h).
Qed.

Definition tensor_assoc_iso {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (x y z : C), is_z_isomorphism (α x y z).

Definition associator_law {C : category} {T : tensor C} (α : associator_data T) : UU :=
  (tensor_assoc_nat_leftwhisker α) × (tensor_assoc_nat_rightwhisker α) × (tensor_assoc_nat_leftrightwhisker α) × (tensor_assoc_iso α).

Definition tensorassociator_natleft {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat_leftwhisker α := pr1 αl.
Definition tensorassociator_natright {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat_rightwhisker α := pr1 (pr2 αl).
Definition tensorassociator_natleftright {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_nat_leftrightwhisker α := pr1 (pr2 (pr2 αl)).
Definition tensorassociator_iso {C : category} {T : tensor C} {α : associator_data T} (αl : associator_law α) : tensor_assoc_iso α := pr2 (pr2 (pr2 αl)).

Definition leftunitor_nat {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  I ⊗^{ T}_{l} f · lu y = lu x · f.

Lemma nattrans_from_leftunitor {C : category} {T : tensor C} {I : C} {lu : leftunitor_data T I} (lunat : leftunitor_nat lu):
  nat_trans (leftwhiskering_functor T (bifunctor_leftid T) (bifunctor_leftcomp T) I) (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (nattransdata_from_leftunitordata lu).
  - exact (λ x y f, lunat x y f).
Defined.

Definition leftunitor_iso {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) : UU :=
  ∏ (x : C), is_z_isomorphism (lu x).

Definition leftunitor_law {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) : UU :=
  leftunitor_nat lu × leftunitor_iso lu.

Definition leftunitornat_from_leftunitorlaw {C : category} {T : tensor C} {I : C} {lu : leftunitor_data T I} (lul : leftunitor_law lu) : leftunitor_nat lu := pr1 lul.

Definition leftunitoriso_from_leftunitorlaw {C : category} {T : tensor C} {I : C} {lu : leftunitor_data T I} (lul : leftunitor_law lu) : leftunitor_iso lu := pr2 lul.

Definition rightunitor_nat {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  f ⊗^{ T}_{r} I · ru y = ru x · f.

Definition nattrans_from_rightunitor {C : category} {T : tensor C} {I : C} {ru : rightunitor_data T I} (runat : rightunitor_nat ru) :
  nat_trans (rightwhiskering_functor T (bifunctor_rightid T) (bifunctor_rightcomp T) I) (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (nattransdata_from_rightunitordata ru).
  - exact (λ x y f, runat x y f).
Defined.

Definition rightunitor_iso {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) : UU :=
  ∏ (x : C), is_z_isomorphism (ru x).

Definition rightunitor_law {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) : UU :=
  rightunitor_nat ru × rightunitor_iso ru.

Definition rightunitornat_from_rightunitorlaw {C : category} {T : tensor C} {I : C} {ru : rightunitor_data T I} (rul : rightunitor_law ru) : rightunitor_nat ru := pr1 rul.

Definition rightunitoriso_from_rightunitorlaw {C : category} {T : tensor C} {I : C} {ru : rightunitor_data T I} (rul : rightunitor_law ru) : rightunitor_iso ru := pr2 rul.

Definition triangle_identity {C : category}
           {T : tensor C}
           {I : C}
           (lu : leftunitor_data T I)
           (ru : rightunitor_data T I)
           (α : associator_data T)
    := ∏ (x y : C), (α x I y) · (x ⊗^{T}_{l} (lu y)) = (ru x) ⊗^{T}_{r} y.

Definition pentagon_identity {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (w x y z : C),
    ((α w x y) ⊗^{T}_{r} z)·(α w (x⊗_{T} y) z)·(w ⊗^{T}_{l} (α x y z)) =  (α (w⊗_{T}x) y z)·(α w x (y ⊗_{T} z)).

Definition monoidal_laws {C : category} (MD : monoidalcategory_data C) : UU :=
   (associator_law α_{MD}) × (leftunitor_law lu_{MD}) × (rightunitor_law ru_{MD})
                       × (triangle_identity lu_{MD} ru_{MD} α_{MD}) × (pentagon_identity α_{MD}).

Definition monoidalcategory (C : category) : UU :=
  ∑ (MD : monoidalcategory_data C), (monoidal_laws MD).

Definition monoidalcategorydata_from_moncat {C : category} (M : monoidalcategory C) : monoidalcategory_data C := pr1 M.
Coercion monoidalcategorydata_from_moncat : monoidalcategory >-> monoidalcategory_data.

Definition monoidallaws_from_moncat {C : category} (M : monoidalcategory C) : monoidal_laws M := pr2 M.

Definition moncat_associatorlaw {C : category} (M : monoidalcategory C) : associator_law α_{M} := pr1 (monoidallaws_from_moncat M).
Definition moncat_leftunitorlaw {C : category} (M : monoidalcategory C) : leftunitor_law lu_{M} := pr1 (pr2 (monoidallaws_from_moncat M)).
Definition moncat_rightunitorlaw {C : category} (M : monoidalcategory C) : rightunitor_law ru_{M} := pr1(pr2 (pr2 (monoidallaws_from_moncat M))).
Definition moncat_triangleidentity {C : category} (M : monoidalcategory C) : triangle_identity lu_{M} ru_{M} α_{M} := pr1 (pr2 (pr2 (pr2 (monoidallaws_from_moncat M)))).
Definition moncat_pentagonidentity {C : category} (M : monoidalcategory C) : pentagon_identity α_{M} := pr2 (pr2 (pr2 (pr2 (monoidallaws_from_moncat M)))).

Module MonoidalCategoryNotations.
  Notation "I_{ M }" := (unit_from_monoidalcatdata M).
  Notation "lu^{ M }" := (leftunitordata_from_monoidalcatdata M).
  Notation "ru^{ M }" := (rightunitordata_from_monoidalcatdata M).
  Notation "α^{ M }" := (associatordata_from_monoidalcatdata M).
  Notation "lu^{ M }_{ x }" := ( (leftunitordata_from_monoidalcatdata M) x ).
  Notation "ru^{ M }_{ x }" := ( (rightunitordata_from_monoidalcatdata M) x ).
  Notation "α^{ M }_{ x , y , z }" := (associatordata_from_monoidalcatdata M x y z).
End MonoidalCategoryNotations.
