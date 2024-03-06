(***************************************************************************

 Monoidal categories

 In this file, we define the notion of monoidal category. In addition, we
 prove the important laws for monoidal categories.

 The main definition in this file, takes a so-called displayed approach.
 More specifically, we define the notion of a monoidal structure on a
 category. For this notion, we define suitable accessors and we prove the
 laws. Finally, we also provide a bundled notion of monoidal category, which
 is a category together with a monoidal structure for it. The necessary
 accessors and laws are derived from the other notion.

 In this file, we use a whiskered approach. This means that we have two
 operations to tensor with morphisms: a left and a right whiskering. Both of
 these take an object and a morphism as input and they return a morphism as
 output.

 Contents
 1. Monoidal structures
 2. Opposite monoidal category
 3. Equivalences from the tensor and unit
 4. The unitors coincide
 5. Swapping the tensor
 6. More monoidal laws
 7. Bundled approach to monoidal categories

Note: after refactoring on March 10, 2023, the prior Git history of this development is found via
git log -- UniMath/CategoryTheory/Monoidal/MonoidalCategoriesWhiskered.v

 ***************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.

Import BifunctorNotations.

(**
 1. Monoidal structures
 *)
Section A.

(** Data **)
Definition tensor_data (C : category) : UU :=
  bifunctor_data C C C.
Identity Coercion tensorintobifunctor : tensor_data >-> bifunctor_data.

Definition leftunitor_data
           {C : category}
           (T : tensor_data C)
           (I : C)
  : UU
  := ∏ (x : C), C⟦I ⊗_{T} x, x⟧.

Definition leftunitorinv_data
           {C : category}
           (T : tensor_data C)
           (I : C)
  : UU
  := ∏ (x : C), C⟦x, I ⊗_{T} x⟧.

Definition rightunitor_data
           {C : category}
           (T : tensor_data C)
           (I : C)
  : UU
  := ∏ (x : C), C⟦x ⊗_{T} I, x⟧.

Definition rightunitorinv_data
           {C : category}
           (T : tensor_data C)
           (I : C)
  : UU
  := ∏ (x : C), C⟦x, x ⊗_{T} I⟧.

Definition associator_data
           {C : category}
           (T : tensor_data C)
  : UU
  := ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

Definition associatorinv_data
           {C : category}
           (T : tensor_data C)
  : UU
  := ∏ (x y z : C), C ⟦x ⊗_{T} (y ⊗_{T} z), (x ⊗_{T} y) ⊗_{T} z⟧.

Definition monoidal_data (C : category): UU :=
    ∑ (T : tensor_data C) (I : C),
    (leftunitor_data T I) × (leftunitorinv_data T I) ×
    (rightunitor_data T I) × (rightunitorinv_data T I) ×
    (associator_data T) × (associatorinv_data T).

Definition make_monoidal_data
           {C : category}
           {T : tensor_data C}
           {I : C}
           (lu : leftunitor_data T I)
           (luinv : leftunitorinv_data T I)
           (ru : rightunitor_data T I)
           (ruinv : rightunitorinv_data T I)
           (α : associator_data T)
           (αinv : associatorinv_data T)
  : monoidal_data C
  := (T,,I,,lu,,luinv,,ru,,ruinv,,α,,αinv).

Definition monoidal_tensor_data {C : category} (MD : monoidal_data C) : tensor_data C := pr1 MD.
Coercion monoidal_tensor_data : monoidal_data >-> tensor_data.

Definition monoidal_unit {C : category} (MD : monoidal_data C) : C := pr12 MD.
Notation "I_{ MD }" := (monoidal_unit MD).

Definition monoidal_leftunitordata
           {C : category}
           (MD : monoidal_data C)
  : leftunitor_data MD I_{MD}
  := pr1 (pr22 MD).
Notation "lu_{ MD }" := (monoidal_leftunitordata MD).

Definition monoidal_leftunitorinvdata
           {C : category}
           (MD : monoidal_data C)
  : leftunitorinv_data MD I_{MD}
  := pr12 (pr22 MD).
Notation "luinv_{ MD }" := (monoidal_leftunitorinvdata MD).

Definition monoidal_rightunitordata
           {C : category}
           (MD : monoidal_data C)
  : rightunitor_data MD I_{MD}
  := pr122 (pr22 MD).
Notation "ru_{ MD }" := (monoidal_rightunitordata MD).

Definition monoidal_rightunitorinvdata
           {C : category}
           (MD : monoidal_data C)
  : rightunitorinv_data MD I_{MD}
  := pr1 (pr222 (pr22 MD)).
Notation "ruinv_{ MD }" := (monoidal_rightunitorinvdata MD).

Definition monoidal_associatordata
           {C : category}
           (MD : monoidal_data C)
  : associator_data MD
  := pr12 (pr222 (pr22 MD)).
Notation "α_{ MD }" := (monoidal_associatordata MD).

Definition monoidal_associatorinvdata
           {C : category}
           (MD : monoidal_data C)
  : associatorinv_data MD
  := pr22 (pr222 (pr22 MD)).
Notation "αinv_{ MD }" := (monoidal_associatorinvdata MD).

(** Axioms **)
Definition leftunitor_nat
           {C : category}
           {T : tensor_data C}
           {I : C}
           (lu : leftunitor_data T I)
  : UU
  := ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  I ⊗^{ T}_{l} f · lu y = lu x · f.

Definition leftunitorinv_nat
           {C : category}
           {T : tensor_data C}
           {I : C}
           (luinv : leftunitorinv_data T I)
  : UU
  := ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  luinv x · I ⊗^{ T}_{l} f = f · luinv y.

Definition leftunitor_iso_law
           {C : category}
           {T : tensor_data C}
           {I : C}
           (lu : leftunitor_data T I)
           (luinv : leftunitorinv_data T I)
  : UU
  := ∏ (x : C), is_inverse_in_precat (lu x) (luinv x).

Definition leftunitor_law
           {C : category}
           {T : tensor_data C}
           {I : C}
           (lu : leftunitor_data T I)
           (luinv : leftunitorinv_data T I)
  : UU
  := leftunitor_nat lu × leftunitor_iso_law lu luinv.

Definition leftunitorlaw_nat
            {C : category}
            {T : tensor_data C}
            {I : C}
            {lu : leftunitor_data T I}
            {luinv : leftunitorinv_data T I}
            (lu_law : leftunitor_law lu luinv)
  : leftunitor_nat lu
  := pr1 lu_law.

Definition leftunitorlaw_iso_law
           {C : category}
           {T : tensor_data C}
           {I : C}
           {lu : leftunitor_data T I}
           {luinv : leftunitorinv_data T I}
           (lu_law : leftunitor_law lu luinv)
  : leftunitor_iso_law lu luinv
  := pr2 lu_law.

Definition rightunitor_nat
           {C : category}
           {T : tensor_data C}
           {I : C}
           (ru : rightunitor_data T I)
  : UU
  := ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  f ⊗^{ T}_{r} I · ru y = ru x · f.

Definition rightunitorinv_nat
           {C : category}
           {T : tensor_data C}
           {I : C}
           (ruinv : rightunitorinv_data T I)
  : UU
  := ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  ruinv x · f ⊗^{ T}_{r} I = f · ruinv y.

Definition rightunitor_iso_law
           {C : category}
           {T : tensor_data C}
           {I : C}
           (ru : rightunitor_data T I)
           (ruinv : rightunitorinv_data T I)
  : UU
  := ∏ (x : C), is_inverse_in_precat (ru x) (ruinv x).

Definition rightunitor_law
           {C : category}
           {T : tensor_data C}
           {I : C}
           (ru : rightunitor_data T I)
           (ruinv : rightunitorinv_data T I)
  : UU
  := rightunitor_nat ru × rightunitor_iso_law ru ruinv.

Definition rightunitorlaw_nat
           {C : category}
           {T : tensor_data C}
           {I : C}
           {ru : rightunitor_data T I}
           {ruinv : rightunitorinv_data T I}
           (rul : rightunitor_law ru ruinv)
  : rightunitor_nat ru
  := pr1 rul.

Definition rightunitorlaw_iso_law
           {C : category}
           {T : tensor_data C}
           {I : C}
           {ru : rightunitor_data T I}
           {ruinv : rightunitorinv_data T I}
           (rul : rightunitor_law ru ruinv)
  : rightunitor_iso_law ru ruinv
  := pr2 rul.

Definition associator_nat_leftwhisker
           {C : category}
           {T : tensor_data C}
           (α : associator_data T)
  : UU
  := ∏ (x y z z' : C) (h : C⟦z,z'⟧),
     (α x y z) · (x ⊗^{ T}_{l} (y ⊗^{ T}_{l} h))
     =
     ((x ⊗_{ T} y) ⊗^{ T}_{l} h) · (α x y z').

Definition associator_nat_rightwhisker
           {C : category}
           {T : tensor_data C}
           (α : associator_data T)
  : UU
  := ∏ (x x' y z : C) (f : C⟦x,x'⟧),
     (α x y z) · (f ⊗^{ T}_{r} (y ⊗_{ T} z))
     =
     ((f ⊗^{ T}_{r} y) ⊗^{ T}_{r} z) · (α x' y z).

Definition associator_nat_leftrightwhisker
           {C : category}
           {T : tensor_data C}
           (α : associator_data T)
  : UU
  := ∏ (x y y' z : C) (g : C⟦y,y'⟧),
     (α x y z) · (x ⊗^{ T}_{l} (g ⊗^{ T}_{r} z))
     =
     ((x ⊗^{ T}_{l} g) ⊗^{ T}_{r} z) · (α x y' z).

Definition associator_iso_law
           {C : category}
           {T : tensor_data C}
           (α : associator_data T)
           (αinv : associatorinv_data T)
  : UU
  := ∏ (x y z : C), is_inverse_in_precat (α x y z) (αinv x y z).

Definition associator_law
           {C : category}
           {T : tensor_data C}
           (α : associator_data T)
           (αinv : associatorinv_data T)
  : UU
  := (associator_nat_leftwhisker α) × (associator_nat_rightwhisker α) ×
     (associator_nat_leftrightwhisker α) × (associator_iso_law α αinv).

Definition associatorlaw_natleft
           {C : category}
           {T : tensor_data C}
           {α : associator_data T}
           {αinv : associatorinv_data T}
           (αl : associator_law α αinv)
  : associator_nat_leftwhisker α
  := pr1 αl.

Definition associatorlaw_natright
           {C : category}
           {T : tensor_data C}
           {α : associator_data T}
           {αinv : associatorinv_data T}
           (αl : associator_law α αinv)
  : associator_nat_rightwhisker α
  := pr1 (pr2 αl).

Definition associatorlaw_natleftright
           {C : category}
           {T : tensor_data C}
           {α : associator_data T}
           {αinv : associatorinv_data T}
           (αl : associator_law α αinv)
  : associator_nat_leftrightwhisker α
  := pr1 (pr2 (pr2 αl)).

Definition associatorlaw_iso_law
           {C : category}
           {T : tensor_data C}
           {α : associator_data T}
           {αinv : associatorinv_data T}
           (αl : associator_law α αinv)
  : associator_iso_law α αinv
  := pr2 (pr2 (pr2 αl)).

Definition triangle_identity
           {C : category}
           {T : tensor_data C}
           {I : C}
           (lu : leftunitor_data T I)
           (ru : rightunitor_data T I)
           (α : associator_data T)
  : UU
  := ∏ (x y : C), α x I y · x ⊗^{T}_{l} (lu y) = ru x ⊗^{T}_{r} y.

(** more triangle laws that are redundant in the axiomatisation *)
Definition triangle_identity'
           {C : category}
           {T : tensor_data C}
           {I : C}
           (lu : leftunitor_data T I)
           (α : associator_data T)
  : UU
  := ∏ (x y : C), α I x y · lu (x ⊗_{T} y) = lu x ⊗^{T}_{r} y.

Definition triangle_identity''
           {C : category}
           {T : tensor_data C}
           {I : C}
           (ru : rightunitor_data T I)
           (α : associator_data T)
  : UU
  := ∏ (x y : C), α x y I · x ⊗^{T}_{l} (ru y) = ru (x ⊗_{T} y).

Definition pentagon_identity
           {C : category}
           {T : tensor_data C}
           (α : associator_data T)
  : UU
  := ∏ (w x y z : C),
     ((α w x y) ⊗^{T}_{r} z) · (α w (x⊗_{T} y) z) · (w ⊗^{T}_{l} (α x y z))
     =
     (α (w⊗_{T}x) y z) · (α w x (y ⊗_{T} z)).

Definition monoidal_laws
           {C : category}
           (MD : monoidal_data C)
  : UU
  := is_bifunctor MD
     × (leftunitor_law lu_{MD} luinv_{MD})
     × (rightunitor_law ru_{MD} ruinv_{MD})
     × (associator_law α_{MD} αinv_{MD})
     × (triangle_identity lu_{MD} ru_{MD} α_{MD})
     × (pentagon_identity α_{MD}).

Definition monoidal (C : category) : UU :=
  ∑ (MD : monoidal_data C), (monoidal_laws MD).

Definition monoidal_mondata {C : category} (M : monoidal C) : monoidal_data C := pr1 M.
Coercion monoidal_mondata : monoidal >-> monoidal_data.

Definition monoidal_monlaws {C : category} (M : monoidal C) : monoidal_laws M := pr2 M.

Definition monoidal_tensor_is_bifunctor
           {C : category}
           (M : monoidal C)
  : is_bifunctor M
  := pr12 M.

#[reversible=no] Coercion monoidal_tensor
         {C : category}
         (M : monoidal C)
  : bifunctor C C C
  := _ ,, monoidal_tensor_is_bifunctor M.

Definition monoidal_leftunitorlaw
           {C : category}
           (M : monoidal C)
  : leftunitor_law lu_{M} luinv_{M}
  := pr12 (monoidal_monlaws M).

Definition monoidal_leftunitornat
           {C : category}
           (M : monoidal C)
  : leftunitor_nat lu_{M}
  := leftunitorlaw_nat (monoidal_leftunitorlaw M).

Definition monoidal_leftunitorisolaw
           {C : category}
           (M : monoidal C)
  : leftunitor_iso_law lu_{M} luinv_{M}
  := leftunitorlaw_iso_law (monoidal_leftunitorlaw M).

Lemma monoidal_leftunitorinvnat
      {C : category}
      (M : monoidal C)
  : leftunitorinv_nat luinv_{M}.
Proof.
  intros x y f.
  apply (z_iso_inv_on_right _ _ _ (_,,_,,monoidal_leftunitorisolaw M x)).
  cbn.
  rewrite assoc.
  apply (z_iso_inv_on_left _ _ _ _ (_,,_,,monoidal_leftunitorisolaw M y)).
  apply pathsinv0, monoidal_leftunitornat.
Qed.

Definition monoidal_rightunitorlaw
           {C : category}
           (M : monoidal C)
  : rightunitor_law ru_{M} ruinv_{M}
  := pr122 (monoidal_monlaws M).

Definition monoidal_rightunitornat
           {C : category}
           (M : monoidal C)
  : rightunitor_nat ru_{M}
  := rightunitorlaw_nat (monoidal_rightunitorlaw M).

Definition monoidal_rightunitorisolaw
           {C : category}
           (M : monoidal C)
  : rightunitor_iso_law ru_{M} ruinv_{M}
  := rightunitorlaw_iso_law (monoidal_rightunitorlaw M).

Lemma monoidal_rightunitorinvnat
      {C : category}
      (M : monoidal C)
  : rightunitorinv_nat ruinv_{M}.
Proof.
  intros x y f.
  apply (z_iso_inv_on_right _ _ _ (_,,_,,monoidal_rightunitorisolaw M x)).
  cbn.
  rewrite assoc.
  apply (z_iso_inv_on_left _ _ _ _ (_,,_,,monoidal_rightunitorisolaw M y)).
  apply pathsinv0, monoidal_rightunitornat.
Qed.

Definition monoidal_associatorlaw
           {C : category}
           (M : monoidal C)
  : associator_law α_{M} αinv_{M}
  := pr1 (pr222 (monoidal_monlaws M)).

Definition monoidal_associatornatleft
           {C : category}
           (M : monoidal C)
  : associator_nat_leftwhisker α_{M}
  := associatorlaw_natleft (monoidal_associatorlaw M).

Definition monoidal_associatornatright
           {C : category}
           (M : monoidal C)
  : associator_nat_rightwhisker α_{M}
  := associatorlaw_natright (monoidal_associatorlaw M).

Definition monoidal_associatornatleftright
           {C : category}
           (M : monoidal C)
  : associator_nat_leftrightwhisker α_{M}
  := associatorlaw_natleftright (monoidal_associatorlaw M).

Definition monoidal_associatorisolaw
           {C : category}
           (M : monoidal C)
  : associator_iso_law α_{M} αinv_{M}
  := associatorlaw_iso_law (monoidal_associatorlaw M).

Lemma associator_nat1
      {C : category}
      (M : monoidal C)
      {x x' y y' z z' : C}
      (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧)
  : (monoidal_associatordata M x y z)
    · ((f ⊗^{M}_{r} (y ⊗_{M} z))
    · (x' ⊗^{M}_{l} ((g ⊗^{M}_{r} z) · (y' ⊗^{M}_{l} h))))
    =
    (((f ⊗^{M}_{r} y)
    · (x' ⊗^{M}_{l} g))  ⊗^{M}_{r} z)
      · ((x' ⊗_{M} y') ⊗^{M}_{l} h) · (monoidal_associatordata M x' y' z').
Proof.
  rewrite assoc.
  rewrite (monoidal_associatornatright M).
  rewrite assoc'.
  etrans. {
    apply cancel_precomposition.
    rewrite (bifunctor_leftcomp M).
    rewrite assoc.
    rewrite (monoidal_associatornatleftright M).
    apply idpath.
  }

  etrans. {
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (monoidal_associatornatleft M).
  }
  rewrite assoc.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0.
  rewrite (bifunctor_rightcomp M).
  apply idpath.
Qed.

Lemma associator_nat2
      {C : category}
      (M : monoidal C)
      {x x' y y' z z' : C} (f : C⟦x,x'⟧)
      (g : C⟦y,y'⟧) (h : C⟦z,z'⟧)
  : (monoidal_associatordata M x y z) · (f ⊗^{M} (g ⊗^{M} h))
    =
    ((f ⊗^{M} g) ⊗^{M} h) · (monoidal_associatordata M x' y' z').
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (associator_nat1 M f g h).
Qed.

Definition monoidal_triangleidentity
           {C : category}
           (M : monoidal C)
  : triangle_identity lu_{M} ru_{M} α_{M}
  := pr12 (pr222 (monoidal_monlaws M)).

Definition monoidal_pentagonidentity
           {C : category}
           (M : monoidal C)
  : pentagon_identity α_{M}
  := pr22 (pr222 (monoidal_monlaws M)).

Lemma isaprop_monoidal_laws {C : category} (M : monoidal_data C)
  : isaprop (monoidal_laws M).
Proof.
  repeat (apply isapropdirprod)
  ; repeat (apply impred ; intro)
  ; repeat (try apply C)
  ; repeat (apply isaprop_is_inverse_in_precat).
Qed.

(** Some additional data and properties which one deduces from monoidal categories **)
(* Not the best name though, but here my creativity fails *)
Lemma swap_nat_along_zisos
      {C : category} {x1 x2 y1 y2 : C}
      (p1 : z_iso x1 y1) (p2 : z_iso x2 y2)
  : ∏ (f: C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
    (pr1 p1) · g = f · (pr1 p2) -> g · (inv_from_z_iso p2) = (inv_from_z_iso p1) · f.
Proof.
  intros f g p.
  apply pathsinv0.
  apply z_iso_inv_on_right.
  rewrite assoc.
  apply z_iso_inv_on_left.
  apply p.
Qed.

Lemma leftunitor_nat_z_iso {C : category} (M : monoidal C)
  : nat_z_iso
      (leftwhiskering_functor M I_{M})
      (functor_identity C).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ x, lu_{M} x).
    + exact (λ x y f, monoidal_leftunitornat M x y f).
  - intro x. exists (luinv_{M} x).
    apply (monoidal_leftunitorisolaw M x).
Defined.

Definition rightunitor_nat_z_iso {C : category} (M : monoidal C)
  : nat_z_iso
      (rightwhiskering_functor M I_{M})
      (functor_identity C).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ x, ru_{M} x).
    + exact (λ x y f, monoidal_rightunitornat M x y f).
  - intro x. exists (ruinv_{M} x).
    apply (monoidal_rightunitorisolaw M x).
Defined.

Definition z_iso_from_associator_iso
           {C : category} (M : monoidal C) (x y z : C)
  : z_iso ((x ⊗_{ M} y) ⊗_{ M} z) (x ⊗_{ M} (y ⊗_{ M} z))
  := make_z_iso
       (α_{M} x y z)
       (αinv_{M} x y z)
       (monoidal_associatorisolaw M x y z).

Definition monoidal_associatorinvnatleft
           {C : category}
           (M : monoidal C)
  : ∏ (x y z z' : C) (h : C⟦z,z'⟧),
    (x ⊗^{M}_{l} (y ⊗^{M}_{l} h)) · (αinv_{M} x y z')
    =
    (αinv_{M} x y z) · ((x ⊗_{M} y) ⊗^{M}_{l} h) .
Proof.
  intros x y z z' h.
  apply (swap_nat_along_zisos (z_iso_from_associator_iso M x y z) (z_iso_from_associator_iso M x y z')).
  apply monoidal_associatornatleft.
Qed.

Definition monoidal_associatorinvnatright
           {C : category}
           (M : monoidal C)
  : ∏ (x x' y z: C) (f : C⟦x,x'⟧),
    (f ⊗^{M}_{r} (y ⊗_{M} z)) · (αinv_{M} x' y z)
    =
    (αinv_{M} x y z) · ((f ⊗^{M}_{r} y) ⊗^{M}_{r} z).
Proof.
  intros x x' y z f.
  apply (swap_nat_along_zisos (z_iso_from_associator_iso M x y z) (z_iso_from_associator_iso M x' y z)).
  apply monoidal_associatornatright.
Qed.

Definition monoidal_associatorinvnatleftright
           {C : category}
           (M : monoidal C)
  : ∏ (x y y' z : C) (g : C⟦y,y'⟧),
    (x ⊗^{M}_{l} (g ⊗^{M}_{r} z)) · (αinv_{M} x y' z)
    =
    (αinv_{M} x y z) · ((x ⊗^{M}_{l} g) ⊗^{M}_{r} z).
Proof.
  intros x y y' z g.
  apply (swap_nat_along_zisos (z_iso_from_associator_iso M x y z) (z_iso_from_associator_iso M x y' z)).
  apply monoidal_associatornatleftright.
Qed.

Definition monoidal_associatorinv_nat1
           {C : category}
           (M : monoidal C)
           {x x' y y' z z' : C}
           (f : C⟦x,x'⟧)
           (g : C⟦y,y'⟧)
           (h : C⟦z,z'⟧)
  : ((f ⊗^{M}_{r} (y ⊗_{M} z))
    · (x' ⊗^{M}_{l} ((g ⊗^{M}_{r} z) · (y' ⊗^{M}_{l} h))))
    · (αinv_{M} x' y' z')
    =
    (αinv_{M} x y z)
    · ((((f ⊗^{M}_{r} y)
    · (x' ⊗^{M}_{l} g))  ⊗^{M}_{r} z)
    · ((x' ⊗_{M} y') ⊗^{ M}_{l} h)).
Proof.
  apply (swap_nat_along_zisos
           (z_iso_from_associator_iso M x y z)
           (z_iso_from_associator_iso M x' y' z')
        ).
  unfold z_iso_from_associator_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  unfold pr1.
  apply associator_nat1.
Qed.

Lemma monoidal_associatorinv_nat2
      {C : category}
      (M : monoidal C)
      {x x' y y' z z' : C}
      (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧)
  : (f ⊗^{M} (g ⊗^{M} h)) · (αinv_{M} x' y' z')
    =
    (αinv_{M} x y z) · ((f ⊗^{M} g) ⊗^{M} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  apply monoidal_associatorinv_nat1.
Qed.

Lemma monoidal_triangle_identity_inv
      {C : category}
      (M : monoidal C)
      (x y : C)
  : x ⊗^{M}_{l} luinv_{M} y · αinv_{M} x I_{ M} y = ruinv_{M} x ⊗^{ M}_{r} y.
Proof.
  apply pathsinv0.
  apply (z_iso_inv_on_left _ _ _ _ ((z_iso_from_associator_iso M _ _ _))).
  cbn.
  set (luiy := make_z_iso _ _ (monoidal_leftunitorisolaw M y)).
  set (luixy := functor_on_z_iso (leftwhiskering_functor M x) luiy).
  set (ruix := make_z_iso _ _ (monoidal_rightunitorisolaw M x)).
  set (ruixy := functor_on_z_iso (rightwhiskering_functor M y) ruix).
  apply pathsinv0.
  apply (z_iso_inv_on_right _ _ _ ruixy).
  apply (z_iso_inv_on_left _ _ _ _ luixy).
  exact (! (monoidal_triangleidentity M) x y).
Qed.

(* another proof of the same law - could be deleted in some future: *)
Lemma monoidal_triangle_identity_inv_alt
      {C : category}
      (M : monoidal C)
      (x y : C)
  : x ⊗^{M}_{l} (luinv_{M} y) · αinv_{M} x I_{M} y  = (ruinv_{M} x) ⊗^{M}_{r} y.
Proof.
  transparent assert (auxiso1 : (z_iso (x ⊗_{ M} y) (x ⊗_{ M} (I_{ M} ⊗_{ M} y)))).
  { exists (x ⊗^{M}_{l} (luinv_{M} y)).
    apply (is_z_iso_leftwhiskering_z_iso M).
    exists (lu_{ M} y).
    split; apply monoidal_leftunitorisolaw. }
  transparent assert (auxiso2 : (z_iso (x ⊗_{ M} y) ((x ⊗_{ M} I_{ M}) ⊗_{ M} y))).
  { exists (ruinv_{ M} x ⊗^{ M}_{r} y).
    apply (is_z_iso_rightwhiskering_z_iso M).
    exists (ru_{ M} x).
    split; apply monoidal_rightunitorisolaw. }
  apply pathsinv0, (z_iso_inv_on_left _ _ _ _ (z_iso_from_associator_iso M _ _ _)).
  apply (z_iso_inv_to_left _ _ _ auxiso2).
  apply (z_iso_inv_to_right _ _ _ _ auxiso1).
  apply pathsinv0, monoidal_triangleidentity.
Qed.

Lemma monoidal_pentagon_identity_inv
      {C : category}
      (M : monoidal C)
      (w x y z : C)
  : w ⊗^{ M}_{l} (αinv_{M} x y z)
    · αinv_{M} w (x ⊗_{ M} y) z
    · αinv_{M} w x y ⊗^{ M}_{r} z
    =
    αinv_{M} w x (y ⊗_{ M} z)
    · αinv_{M} (w ⊗_{ M} x) y z.
Proof.
  apply pathsinv0.
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_associator_iso M _ _ _)).
  unfold z_iso_from_associator_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  etrans. { apply (pathsinv0 (id_right _)). }
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_associator_iso M _ _ _)).
  cbn.
  apply pathsinv0.
  etrans. {
   rewrite assoc.
   apply cancel_postcomposition.
   apply (pathsinv0 (monoidal_pentagonidentity M w x y z)).
  }
  etrans. {
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (pathsinv0 (bifunctor_leftcomp M _ _ _ _ _ _)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply cancel_precomposition.
    apply maponpaths.
    apply (pr2 (z_iso_from_associator_iso M x y z)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply cancel_precomposition.
    apply (bifunctor_leftid M).
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply id_right.
  }
  etrans. {
    apply cancel_postcomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (pr2 (z_iso_from_associator_iso M w (x⊗_{M}y) z)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply id_right.
  }
  etrans. {
    apply (pathsinv0 (bifunctor_rightcomp M _ _ _ _ _ _)).
  }
  etrans. {
    apply maponpaths.
    apply (pr2 (pr2 (z_iso_from_associator_iso M w x y))).
  }
  apply (bifunctor_rightid M).
Qed.

End A.

Module MonoidalNotations.
  Notation "I_{ M }" := (monoidal_unit M) : cat.
  Notation "lu_{ M }" := (monoidal_leftunitordata M) : cat.
  Notation "luinv_{ M }" := (monoidal_leftunitorinvdata M) : cat.
  Notation "ru_{ M }" := (monoidal_rightunitordata M) : cat.
  Notation "ruinv_{ M }" := (monoidal_rightunitorinvdata M) : cat.
  Notation "α_{ M }" := (monoidal_associatordata M) : cat.
  Notation "αinv_{ M }" := (monoidal_associatorinvdata M) : cat.
  Notation "lu^{ M }_{ x }" := (monoidal_leftunitordata M x ) : cat.
  Notation "ru^{ M }_{ x }" := ( monoidal_rightunitordata M x ) : cat.
  Notation "α^{ M }_{ x , y , z }" := (monoidal_associatordata M x y z) : cat.
  Notation "luinv^{ M }_{ x }" := (monoidal_leftunitorinvdata M x ) : cat.
  Notation "ruinv^{ M }_{ x }" := ( monoidal_rightunitorinvdata M x ) : cat.
  Notation "αinv^{ M }_{ x , y , z }" := (monoidal_associatorinvdata M x y z) : cat.
End MonoidalNotations.

(**
 2. Opposite monoidal category
 *)
Section OppositeMonoidal.
  Context {C : category} (M : monoidal C).

  Import MonoidalNotations.

  Definition monoidal_opp_tensor_data : bifunctor_data C^op C^op C^op.
  Proof.
    exists (pr11 (monoidal_tensor M)).
    exists (λ x _ _ g, x ⊗^{M}_{l} g).
    exact (λ x _ _ f, f ⊗^{M}_{r} x).
  Defined.

  Lemma monoidal_opp_is_tensor : is_bifunctor monoidal_opp_tensor_data.
  Proof.
    repeat split ; (try (intro ; intros) ; try apply (pr2 (monoidal_tensor M))).
    exact (! bifunctor_equalwhiskers M a2 a1 b2 b1 f g).
  Qed.

  Definition monoidal_opp_tensor : bifunctor C^op C^op C^op
    := monoidal_opp_tensor_data ,, monoidal_opp_is_tensor.

  Definition monoidal_opp_data : monoidal_data C^op.
  Proof.
    exists monoidal_opp_tensor_data.
    exists I_{M}.
    exists luinv_{M}.
    exists lu_{M}.
    exists ruinv_{M}.
    exists ru_{M}.
    exists αinv_{M}.
    exact α_{M}.
  Defined.

  Definition monoidal_opp_laws : monoidal_laws monoidal_opp_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply (bifunctor_leftid M).
    - intro ; intros.
      apply (bifunctor_rightid M).
    - intro ; intros.
      apply (bifunctor_leftcomp M).
    - intro ; intros.
      apply (bifunctor_rightcomp M).
    - intro ; intros.
      exact (!(bifunctor_equalwhiskers M _ _ _ _ f g)).
    - intro ; intros ; apply monoidal_leftunitorinvnat.
    - apply (monoidal_leftunitorisolaw M).
    - apply (monoidal_leftunitorisolaw M).
    - intro ; intros ; apply monoidal_rightunitorinvnat.
    - apply (monoidal_rightunitorisolaw M).
    - apply (monoidal_rightunitorisolaw M).
    - intro ; intros ; apply monoidal_associatorinvnatleft.
    - intro ; intros ; apply monoidal_associatorinvnatright.
    - intro ; intros ; apply monoidal_associatorinvnatleftright.
    - apply (monoidal_associatorisolaw M).
    - apply (monoidal_associatorlaw M).
    - intro ; intros ; apply monoidal_triangle_identity_inv.
    - intros w x y z.
      refine (_ @ monoidal_pentagon_identity_inv M w x y z).
      simpl ; apply assoc.
  Qed.

  Definition monoidal_opp : monoidal C^op
    := monoidal_opp_data ,, monoidal_opp_laws.
End OppositeMonoidal.

(**
 3. Equivalences from the tensor and unit
 *)
Section EquivalenceFromTensorWithUnit.
  Context {C : category} (M : monoidal C).

  Import MonoidalNotations.

  Definition ladjunction_data_from_tensor_with_unit
    : adjunction_data C C.
  Proof.
    exists (leftwhiskering_functor M I_{M}).
    exists (functor_identity C).
    use tpair.
    - apply (nat_z_iso_inv (leftunitor_nat_z_iso M)).
    - apply (leftunitor_nat_z_iso M).
  Defined.

  Definition lequivalence_from_tensor_with_unit
    : equivalence_of_cats C C.
  Proof.
    exists ladjunction_data_from_tensor_with_unit.
    split.
    - intro ; apply (nat_z_iso_inv (leftunitor_nat_z_iso M)).
    - intro ; apply (leftunitor_nat_z_iso M).
  Defined.

  Definition radjunction_data_from_tensor_with_unit
    : adjunction_data C C.
  Proof.
    exists (rightwhiskering_functor M I_{M}).
    exists (functor_identity C).
    use tpair.
    - apply (nat_z_iso_inv (rightunitor_nat_z_iso M)).
    - apply (rightunitor_nat_z_iso M).
  Defined.

  Definition requivalence_from_tensor_with_unit
    : equivalence_of_cats C C.
  Proof.
    exists radjunction_data_from_tensor_with_unit.
    split.
    - intro ; apply (nat_z_iso_inv (rightunitor_nat_z_iso M)).
    - intro ; apply (rightunitor_nat_z_iso M).
  Defined.

  Lemma leftwhiskering_fullyfaithful
    : fully_faithful (leftwhiskering_functor M I_{M}).
  Proof.
    apply fully_faithful_from_equivalence.
    exact (adjointification lequivalence_from_tensor_with_unit).
  Defined.

  Lemma rightwhiskering_fullyfaithful
    : fully_faithful (rightwhiskering_functor M I_{M}).
  Proof.
    apply fully_faithful_from_equivalence.
    exact (adjointification requivalence_from_tensor_with_unit).
  Defined.

  Lemma leftwhiskering_faithful
    : faithful (leftwhiskering_functor M I_{M}).
  Proof.
    exact (pr2 (fully_faithful_implies_full_and_faithful _ _ _ leftwhiskering_fullyfaithful)).
  Defined.

  Lemma rightwhiskering_faithful
    : faithful (rightwhiskering_functor M I_{M}).
  Proof.
    exact (pr2 (fully_faithful_implies_full_and_faithful _ _ _ rightwhiskering_fullyfaithful)).
  Defined.
End EquivalenceFromTensorWithUnit.

(**
 4. The unitors coincide
 *)
Section UnitorsCoincide.
  Context {C : category} (M : monoidal C).

  Import MonoidalNotations.

  Local Lemma lemma0 (x y : C) :
    ((α_{M} I_{M} I_{M} x) ⊗^{M}_{r} y) · ((I_{M} ⊗^{M}_{l} lu_{M} x) ⊗^{M}_{r} y) =
    (ru_{M} I_{M} ⊗^{M}_{r} x) ⊗^{M}_{r} y.
  Proof.
    refine (! bifunctor_rightcomp M _ _ _ _ _ _ @ _).
    apply maponpaths.
    apply (monoidal_triangleidentity M I_{M} x).
  Qed.

  Local Lemma lemma1 (x y : C) :
    α_{M} I_{M} (I_{M} ⊗_{M} x) y · (I_{M} ⊗^{M}_{l} (lu_{M} x ⊗^{M}_{r} y)) =
      ((I_{M} ⊗^{M}_{l} lu_{M} x) ⊗^{M}_{r} y) · α_{M} I_{M} x y.
  Proof.
    apply monoidal_associatornatleftright.
  Qed.

  Local Lemma lemma2 (x y : C) :
    I_{M} ⊗^{M}_{l} (lu_{M} x ⊗^{M}_{r} y) = αinv_{M} I_{M} (I_{M} ⊗_{M} x) y · (((I_{M} ⊗^{M}_{l} lu_{M} x) ⊗^{M}_{r} y) · α_{M} I_{M} x y).
  Proof.
    set (αiso := make_z_iso _ _ (monoidal_associatorisolaw M  I_{ M} (I_{ M} ⊗_{ M} x) y)).
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ αiso).
    apply pathsinv0.
    apply lemma1.
  Qed.

  Local Lemma lemma2' (x y : C) :
    (I_{M} ⊗^{M}_{l} lu_{M} x) ⊗^{M}_{r} y =
      ((αinv_{M} I_{M} I_{M} x) ⊗^{M}_{r} y) · (ru_{M} I_{M} ⊗^{M}_{r} x) ⊗^{M}_{r} y.
  Proof.
    apply pathsinv0.
    set (αiso := make_z_iso _ _ (monoidal_associatorisolaw M  I_{ M} I_{ M} x)).
    set (αisor := functor_on_z_iso (rightwhiskering_functor M y) αiso).
    apply (z_iso_inv_on_right _ _ _ αisor).
    apply pathsinv0.
    apply lemma0.
  Qed.

  Local Lemma lemma3 (x y : C) :
    I_{M} ⊗^{M}_{l} (lu_{M} x ⊗^{M}_{r} y) =
      αinv_{M} I_{M} (I_{M} ⊗_{M} x) y
        · ((((αinv_{M} I_{M} I_{M} x) ⊗^{M}_{r} y)
        · (ru_{M} I_{M} ⊗^{M}_{r} x) ⊗^{M}_{r} y)
        · α_{M} I_{M} x y).
  Proof.
    refine (lemma2 x y @ _).
    apply maponpaths.
    apply maponpaths_2.
    apply lemma2'.
  Qed.

  Local Lemma right_whisker_with_lunitor' (x y : C)
    : I_{M} ⊗^{M}_{l} (lu_{M} x ⊗^{M}_{r} y)
      =
      I_{M} ⊗^{M}_{l} (α_{M} I_{M} x y · lu_{M} (x ⊗_{M} y)).
  Proof.
    refine (lemma3 x y @ _).
    set (αiso := make_z_iso _ _ (monoidal_associatorisolaw M  I_{ M} (I_{ M} ⊗_{M} x) y)).
    apply (z_iso_inv_on_right _ _ _ αiso).
    set (αiso' := make_z_iso _ _ (monoidal_associatorisolaw M  I_{ M} I_{ M} x)).
    set (αisor := functor_on_z_iso (rightwhiskering_functor M y) αiso').
    etrans. { apply assoc'. }
    apply (z_iso_inv_on_right _ _ _ αisor).
    apply pathsinv0.
    simpl.

    etrans. { apply assoc. }
    etrans.
    {
      apply maponpaths.
      apply (bifunctor_leftcomp M _ _ _ _ _ _).
    }

    etrans. { apply assoc. }
    etrans. {
      apply maponpaths_2.
      apply (monoidal_pentagonidentity M I_{M} I_{M} x y).
    }

    etrans.
    2: {
      apply (associatorlaw_natright (monoidal_associatorlaw M)).
    }

    etrans. { apply assoc'. }
    apply maponpaths.
    apply monoidal_triangleidentity.
  Qed.

  Lemma right_whisker_with_lunitor : triangle_identity' lu_{M} α_{M}.
  Proof.
    intros x y.
    use faithful_reflects_commutative_triangle.
    3: { apply leftwhiskering_faithful. }
    apply pathsinv0.
    refine (right_whisker_with_lunitor' _ _ @ _).
    apply (bifunctor_leftcomp (monoidal_tensor M)).
  Qed.

  Definition monoidal_triangleidentity' := right_whisker_with_lunitor.

  Lemma monoidal_triangle_identity'_inv (x y : C)
  : luinv_{M} (x ⊗_{M} y) · αinv_{M} I_{M} x y = luinv_{M} x ⊗^{M}_{r} y.
  Proof.
    apply pathsinv0.
    apply (z_iso_inv_on_left _ _ _ _ ((z_iso_from_associator_iso M _ _ _))).
    cbn.
    set (luix := make_z_iso _ _ (monoidal_leftunitorisolaw M x)).
    set (luixy := functor_on_z_iso (rightwhiskering_functor M y) luix).
    set (luipxy := make_z_iso _ _ (monoidal_leftunitorisolaw M (x ⊗_{ M} y))).
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ luixy).
    apply (z_iso_inv_on_left _ _ _ _ luipxy).
    exact (! monoidal_triangleidentity' x y).
  Qed.

  Lemma lunitor_preserves_leftwhiskering_with_unit
    : lu^{M}_{I_{ M} ⊗_{M} I_{M}} = I_{M} ⊗^{ M}_{l} lu^{M}_{I_{ M}}.
  Proof.
    apply pathsinv0.
    set (lun := monoidal_leftunitornat M _ _ (lu_{M} (I_{M}))).
    etrans. { apply (! id_right _). }
    etrans.
    2: { apply id_right. }

    etrans. {
      apply maponpaths.
      exact (! pr1 (monoidal_leftunitorisolaw M I_{ M})).
    }
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2 ; exact lun. }
    etrans. { apply assoc'. }
    apply maponpaths.
    apply monoidal_leftunitorisolaw.
  Qed.

  Lemma unitors_coincide_on_unit'
    : lu_{M} I_{M} ⊗^{M}_{r} I_{M} = ru_{M} I_{M} ⊗^{M}_{r} I_{M}.
  Proof.
    refine (! right_whisker_with_lunitor I_{M} I_{M} @ _).
    refine (_ @ monoidal_triangleidentity M I_{M} I_{M}).
    apply maponpaths.
    apply lunitor_preserves_leftwhiskering_with_unit.
  Qed.

  Lemma unitors_coincide_on_unit
    : lu_{M} I_{M} = ru_{M} I_{M}.
  Proof.
    use faithful_reflects_morphism_equality.
    3: { apply rightwhiskering_faithful. }
    apply unitors_coincide_on_unit'.
  Qed.

  Corollary unitorsinv_coincide_on_unit
    : luinv_{M} I_{M} = ruinv_{M} I_{M}.
  Proof.
    apply (cancel_z_iso _ _ (lu_{M} I_{M},,(luinv_{M} I_{M},,monoidal_leftunitorisolaw M I_{M}))).
    cbn.
    etrans.
    2: { rewrite unitors_coincide_on_unit.
         apply pathsinv0, (monoidal_rightunitorisolaw M I_{M}). }
    apply (monoidal_leftunitorisolaw M I_{M}).
  Qed.
End UnitorsCoincide.

(* Using the lemma for a different category, hence outside of the section. *)

Section UnitorsCoincideAlternative.
  Import MonoidalNotations.

  Lemma unitorsinv_coincide_on_unit_alt {C : category} (M : monoidal C)
    : luinv_{M} I_{M} = ruinv_{M} I_{M}.
  Proof.
    exact (unitors_coincide_on_unit (monoidal_opp M)).
  Qed.
End UnitorsCoincideAlternative.

(**
 5. Swapping the tensor
 *)
Section MonoidalSwapped.
  Import MonoidalNotations.

  Definition tensor_swapped {V : category} (Mon_V : monoidal V)
    : tensor_data V.
  Proof.
    repeat (use tpair).
    - intros v w.
      exact (w ⊗_{Mon_V} v).
    - intros v w1 w2 f.
      exact (f ⊗^{Mon_V}_{r} v).
    - intros v w1 w2 f.
      exact (v ⊗^{Mon_V}_{l} f).
  Defined.

  Definition monoidal_swapped_data {V : category} (Mon_V : monoidal V)
    : monoidal_data V.
  Proof.
    exists (tensor_swapped Mon_V).
    exists I_{Mon_V}.
    exists (λ v, ru_{Mon_V} v).
    exists (λ v, ruinv_{Mon_V} v).
    exists (λ v, lu_{Mon_V} v).
    exists (λ v, luinv_{Mon_V} v).
    exists (λ v1 v2 v3, αinv_{Mon_V} v3 v2 v1).
    exact (λ v1 v2 v3, α_{Mon_V} v3 v2 v1).
  Defined.

  Lemma monoidal_swapped_laws {V : category} (Mon_V : monoidal V)
    : monoidal_laws (monoidal_swapped_data Mon_V).
  Proof.
    repeat split.
    - intro ; intro ; apply (bifunctor_rightid Mon_V).
    - intro ; intro ; apply (bifunctor_leftid Mon_V).
    - intro ; intros ; apply (bifunctor_rightcomp Mon_V).
    - intro ; intros ; apply (bifunctor_leftcomp Mon_V).
    - intro ; intros ; apply (! bifunctor_equalwhiskers Mon_V _ _ _ _ _ _).
    - intro ; intros ; apply monoidal_rightunitornat.
    - apply monoidal_rightunitorisolaw.
    - apply monoidal_rightunitorisolaw.
    - intro ; intros ; apply monoidal_leftunitornat.
    - apply monoidal_leftunitorisolaw.
    - apply monoidal_leftunitorisolaw.
    - intro ; intros ; apply (! monoidal_associatorinvnatright Mon_V _ _ _ _ _).
    - intro ; intros ; apply (! monoidal_associatorinvnatleft Mon_V _ _ _ _ _).
    - intro ; intros ; apply (! monoidal_associatorinvnatleftright Mon_V _ _ _ _ _).
    - apply monoidal_associatorisolaw.
    - apply monoidal_associatorisolaw.
    - intro ; intros.
      cbn.
      rewrite (! monoidal_triangleidentity Mon_V _ _).
      rewrite assoc.
      rewrite (pr2 (monoidal_associatorisolaw Mon_V _ _ _)).
      apply id_left.
    - intro ; intros ; apply monoidal_pentagon_identity_inv.
  Qed.

  Definition monoidal_swapped {V : category} (Mon_V : monoidal V)
    : monoidal V
    := monoidal_swapped_data Mon_V ,, monoidal_swapped_laws Mon_V.
End MonoidalSwapped.

(**
 6. More monoidal laws
 *)
Section MonoidalLaws.
  Import MonoidalNotations.

  Lemma left_whisker_with_runitor {C : category} (M : monoidal C)
    : triangle_identity'' ru_{M} α_{M}.
  Proof.
    red; intros x y.
    assert (aux := right_whisker_with_lunitor (monoidal_swapped M) y x).
    cbn in aux.
    rewrite <- aux.
    rewrite assoc.
    etrans.
    { apply cancel_postcomposition.
      apply monoidal_associatorisolaw. }
    apply id_left.
  Qed.

  Lemma monoidal_triangle_identity''_inv {C : category} (M : monoidal C) (x y : C)
    : x ⊗^{M}_{l} (ruinv_{M} y) · αinv_{M} x y I_{M} = ruinv_{M} (x ⊗_{M} y).
  Proof.
    apply pathsinv0.
    apply (z_iso_inv_on_left _ _ _ _ ((z_iso_from_associator_iso M _ _ _))).
    cbn.
    set (ruiy := make_z_iso _ _ (monoidal_rightunitorisolaw M y)).
    set (ruiyx := functor_on_z_iso (leftwhiskering_functor M x) ruiy).
    set (ruipxy := make_z_iso _ _ (monoidal_rightunitorisolaw M (x ⊗_{ M} y))).
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ ruipxy).
    apply (z_iso_inv_on_left _ _ _ _ ruiyx).
    exact (! (left_whisker_with_runitor M) x y).
  Qed.

  Lemma lunitorinv_preserves_leftwhiskering_with_unit
    {C : category} (M : monoidal C)
    : luinv^{M}_{I_{ M}} ⊗^{ M}_{r} I_{ M} · α^{ M }_{ I_{ M}, I_{ M}, I_{ M}}
      = I_{ M} ⊗^{ M}_{l} luinv^{M}_{I_{ M}}.
  Proof.
    set (t := monoidal_triangle_identity_inv_alt M I_{M} I_{M}).

    use (_ @ ! z_iso_inv_on_left _ _ _ _ (_,, α^{M}_{_,_,_} ,, _) _ (! t)).
    - apply maponpaths_2.
      apply maponpaths.
      apply unitorsinv_coincide_on_unit_alt.
    - split ; apply (monoidal_associatorisolaw M).
  Qed.
 End MonoidalLaws.

(**
 7. Bundled approach to monoidal categories
 *)
(** Accessors and notations for monoidal categories *)
Declare Scope moncat.
Local Open Scope moncat.

Definition monoidal_cat : UU := ∑ (C : category), monoidal C.

#[reversible=no] Coercion monoidal_cat_to_cat (V : monoidal_cat) : category := pr1 V.
#[reversible=no] Coercion monoidal_cat_to_monoidal (V : monoidal_cat) : monoidal V := pr2 V.

Definition monoidal_cat_tensor_pt
           {V : monoidal_cat}
           (x y : V)
  : V
  := x ⊗_{ pr2 V } y.

Notation "x ⊗ y" :=  (monoidal_cat_tensor_pt x y) : moncat.

Definition monoidal_cat_tensor_mor
           {V : monoidal_cat}
           {x₁ x₂ y₁ y₂ : V}
           (f : x₁ --> x₂)
           (g : y₁ --> y₂)
  : x₁ ⊗ y₁ --> x₂ ⊗ y₂
  := f ⊗^{ pr2 V } g.

Notation "f #⊗ g" := (monoidal_cat_tensor_mor f g) (at level 31) : moncat.

Proposition tensor_mor_left
            {V : monoidal_cat}
            (x : V)
            {y z : V}
            (f : y --> z)
  : x ⊗^{V}_{l} f = identity x #⊗ f.
Proof.
  unfold monoidal_cat_tensor_mor.
  unfold functoronmorphisms1.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply (bifunctor_rightid V).
  }
  apply id_left.
Qed.

Proposition tensor_mor_right
            {V : monoidal_cat}
            (x : V)
            {y z : V}
            (f : y --> z)
  : f ⊗^{V}_{r} x = f #⊗ identity x.
Proof.
  unfold monoidal_cat_tensor_mor.
  unfold functoronmorphisms1.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply (bifunctor_leftid V).
  }
  apply id_right.
Qed.

Section MonoidalCatAccessors.
  Context {V : monoidal_cat}.

  Import MonoidalNotations.

  Definition tensor_id_id
             (x y : V)
    : identity x #⊗ identity y = identity (x ⊗ y).
  Proof.
    apply bifunctor_distributes_over_id.
    - apply (bifunctor_leftid V).
    - apply (bifunctor_rightid V).
  Qed.

  Definition tensor_comp_mor
             {x₁ x₂ x₃ y₁ y₂ y₃ : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : (f · f') #⊗ (g · g') = f #⊗ g · f' #⊗ g'.
  Proof.
    use bifunctor_distributes_over_comp.
    - apply (bifunctor_leftcomp V).
    - apply (bifunctor_rightcomp V).
    - apply (bifunctor_equalwhiskers V).
  Qed.

  Definition tensor_comp_id_l
             {x y₁ y₂ y₃ : V}
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : (identity x) #⊗ (g · g') = (identity x) #⊗ g · (identity x) #⊗ g'.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_l_id_l
             {x₁ x₂ y₁ y₂ y₃ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : f #⊗ (g · g') = (identity _) #⊗ g · f #⊗ g'.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_l_id_r
             {x₁ x₂ y₁ y₂ y₃ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : f #⊗ (g · g') = f #⊗ g · (identity _) #⊗ g'.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition tensor_comp_id_r
             {x₁ x₂ x₃ y : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
    : (f · f') #⊗ (identity y) = f #⊗ (identity y) · f' #⊗ (identity y).
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_r_id_l
             {x₁ x₂ x₃ y₁ y₂ : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
             (g : y₁ --> y₂)
    : (f · f') #⊗ g = f #⊗ (identity _) · f' #⊗ g.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_r_id_r
             {x₁ x₂ x₃ y₁ y₂ : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
             (g : y₁ --> y₂)
    : (f · f') #⊗ g = f #⊗ g · f' #⊗ (identity _).
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition tensor_split
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : f #⊗ g = identity _ #⊗ g · f #⊗ identity _.
  Proof.
    refine (_ @ tensor_comp_mor _ _ _ _).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Definition tensor_split'
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : f #⊗ g = f #⊗ identity _ · identity _ #⊗ g.
  Proof.
    refine (_ @ tensor_comp_mor _ _ _ _).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Definition tensor_swap
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : f #⊗ identity _ · identity _ #⊗ g = identity _ #⊗ g · f #⊗ identity _.
  Proof.
    rewrite <- tensor_split, <- tensor_split'.
    apply idpath.
  Qed.

  Definition tensor_swap'
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : identity _ #⊗ g · f #⊗ identity _ = f #⊗ identity _ · identity _ #⊗ g.
  Proof.
    rewrite <- tensor_split, <- tensor_split'.
    apply idpath.
  Qed.

  Definition mon_lunitor
             (x : V)
    : I_{V} ⊗ x --> x
    := monoidal_leftunitordata V x.

  Definition tensor_lunitor
             {x y : V}
             (f : x --> y)
    : identity _ #⊗ f · mon_lunitor y
      =
      mon_lunitor x · f.
  Proof.
    refine (_ @ pr1 (monoidal_leftunitorlaw V) x y f).
    apply maponpaths_2.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (bifunctor_rightid V).
  Qed.

  Definition mon_linvunitor
             (x : V)
    : x --> I_{V} ⊗ x
    := monoidal_leftunitorinvdata V x.

  Definition tensor_linvunitor
             {x y : V}
             (f : x --> y)
    : f · mon_linvunitor y
      =
      mon_linvunitor x · identity _ #⊗ f.
  Proof.
    refine (!(monoidal_leftunitorinvnat V x y f) @ _).
    apply maponpaths.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    refine (!_).
    apply (bifunctor_rightid V).
  Qed.

  Definition mon_lunitor_linvunitor
             (x : V)
    : mon_lunitor x · mon_linvunitor x = identity _.
  Proof.
    exact (pr1 (monoidal_leftunitorisolaw V x)).
  Qed.

  Definition mon_linvunitor_lunitor
             (x : V)
    : mon_linvunitor x · mon_lunitor x = identity _.
  Proof.
    exact (pr2 (monoidal_leftunitorisolaw V x)).
  Qed.

  Definition mon_runitor
             (x : V)
    : x ⊗ I_{V} --> x
    := monoidal_rightunitordata V x.

  Definition tensor_runitor
             {x y : V}
             (f : x --> y)
    : f #⊗ identity _ · mon_runitor y
      =
      mon_runitor x · f.
  Proof.
    refine (_ @ pr1 (monoidal_rightunitorlaw V) x y f).
    apply maponpaths_2.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (_ @ id_right _).
    apply maponpaths.
    apply (bifunctor_leftid V).
  Qed.

  Definition mon_rinvunitor
             (x : V)
    : x --> x ⊗ I_{V}
    := monoidal_rightunitorinvdata V x.

  Definition tensor_rinvunitor
             {x y : V}
             (f : x --> y)
    : f · mon_rinvunitor y
      =
      mon_rinvunitor x · f #⊗ identity _.
  Proof.
    refine (!(monoidal_rightunitorinvnat V x y f) @ _).
    apply maponpaths.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    apply (bifunctor_leftid V).
  Qed.

  Definition mon_runitor_rinvunitor
             (x : V)
    : mon_runitor x · mon_rinvunitor x = identity _.
  Proof.
    exact (pr1 (monoidal_rightunitorisolaw V x)).
  Qed.

  Definition mon_rinvunitor_runitor
             (x : V)
    : mon_rinvunitor x · mon_runitor x = identity _.
  Proof.
    exact (pr2 (monoidal_rightunitorisolaw V x)).
  Qed.

  Definition mon_lassociator
             (x y z : V)
    : (x ⊗ y) ⊗ z --> x ⊗ (y ⊗ z)
    := α_{ V } x y z.

  Definition tensor_lassociator
             {x₁ x₂ y₁ y₂ z₁ z₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
             (h : z₁ --> z₂)
    : (f #⊗ g) #⊗ h · mon_lassociator _ _ _
      =
      mon_lassociator _ _ _ · f #⊗ (g #⊗ h).
  Proof.
    refine (!_).
    apply associator_nat2.
  Qed.

  Definition mon_rassociator
             (x y z : V)
    : x ⊗ (y ⊗ z) --> (x ⊗ y) ⊗ z
    := αinv_{ V } x y z.

  Definition tensor_rassociator
             {x₁ x₂ y₁ y₂ z₁ z₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
             (h : z₁ --> z₂)
    : f #⊗ (g #⊗ h) · mon_rassociator _ _ _
      =
      mon_rassociator _ _ _ · (f #⊗ g) #⊗ h.
  Proof.
    exact (monoidal_associatorinv_nat2 V f g h).
  Qed.

  Definition mon_lassociator_rassociator
             (x y z : V)
    : mon_lassociator x y z · mon_rassociator x y z = identity _.
  Proof.
    exact (pr1 (monoidal_associatorisolaw V x y z)).
  Qed.

  Definition mon_rassociator_lassociator
             (x y z : V)
    : mon_rassociator x y z · mon_lassociator x y z = identity _.
  Proof.
    exact (pr2 (monoidal_associatorisolaw V x y z)).
  Qed.

  Definition mon_triangle
             (x y : V)
    : mon_runitor x #⊗ identity y
      =
      mon_lassociator x I_{V} y · (identity x #⊗ mon_lunitor y).
  Proof.
    refine (_ @ !(monoidal_triangleidentity V x y) @ _).
    - unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (bifunctor_leftid V).
    - apply maponpaths.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      refine (!_).
      apply (bifunctor_rightid V).
  Qed.

  Definition mon_inv_triangle
             (x y : V)
    : identity x #⊗ mon_linvunitor y
      =
      mon_rinvunitor x #⊗ identity y · mon_lassociator x (I_{V}) y.
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (_ @ !(monoidal_triangle_identity_inv V x y)).
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (bifunctor_leftid V).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_rassociator_lassociator.
    }
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite (whiskerscommutes V).
    - apply maponpaths.
      refine (!_).
      apply (bifunctor_rightid V).
    - apply (bifunctor_equalwhiskers V).
  Qed.

  Definition mon_lunitor_triangle
             (x y : V)
    : mon_lassociator (I_{V}) x y · mon_lunitor (x ⊗ y)
      =
      mon_lunitor x #⊗ identity y.
  Proof.
    refine (right_whisker_with_lunitor V x y @ _).
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    apply (bifunctor_leftid V).
  Qed.

  Definition mon_linvunitor_triangle
             (x y : V)
    : mon_linvunitor x #⊗ identity y · mon_lassociator (I_{V}) x y
      =
      mon_linvunitor (x ⊗ y).
  Proof.
    refine (!(id_right _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(mon_lunitor_linvunitor _)).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply mon_lunitor_triangle.
    }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite <- tensor_comp_id_r.
    rewrite mon_linvunitor_lunitor.
    apply tensor_id_id.
  Qed.

  Definition mon_runitor_triangle
             (x y : V)
    : mon_rassociator x y (I_{V}) · mon_runitor (x ⊗ y)
      =
      identity x #⊗ mon_runitor y.
  Proof.
    etrans.
    {
      apply maponpaths.
      exact (!(left_whisker_with_runitor V x y)).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply mon_rassociator_lassociator.
    }
    rewrite id_left.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    refine (!_).
    apply (bifunctor_rightid V).
  Qed.

  Definition mon_rinvunitor_triangle
             (x y : V)
    : identity x #⊗ mon_rinvunitor y · mon_rassociator x y (I_{V})
      =
      mon_rinvunitor (x ⊗ y).
  Proof.
    refine (!(id_right _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(mon_runitor_rinvunitor _)).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply mon_runitor_triangle.
    }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite <- tensor_comp_id_l.
    rewrite mon_rinvunitor_runitor.
    apply tensor_id_id.
  Qed.

  Definition mon_runitor_I_mon_lunitor_I
    : mon_runitor (I_{V}) = mon_lunitor (I_{V}).
  Proof.
    refine (!_).
    apply unitors_coincide_on_unit.
  Qed.

  Definition mon_lunitor_I_mon_runitor_I
    : mon_lunitor (I_{V}) = mon_runitor (I_{V}).
  Proof.
    rewrite mon_runitor_I_mon_lunitor_I.
    apply idpath.
  Qed.

  Definition mon_rinvunitor_I_mon_linvunitor_I
    : mon_rinvunitor (I_{V}) = mon_linvunitor (I_{V}).
  Proof.
    cbn.
    refine (!_).
    apply unitorsinv_coincide_on_unit.
  Qed.

  Definition mon_linvunitor_I_mon_rinvunitor_I
    : mon_linvunitor (I_{V}) = mon_rinvunitor (I_{V}).
  Proof.
    rewrite mon_rinvunitor_I_mon_linvunitor_I.
    apply idpath.
  Qed.

  Proposition mon_lassociator_lassociator
              {w x y z : V}
    : mon_lassociator (w ⊗ x) y z
      · mon_lassociator w x (y ⊗ z)
      =
      mon_lassociator w x y #⊗ identity z
      · mon_lassociator w (x ⊗ y) z
      · identity w #⊗ mon_lassociator x y z.
  Proof.
    refine (!(monoidal_pentagonidentity V w x y z) @ _).
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite (bifunctor_rightid V).
    rewrite (bifunctor_leftid V).
    rewrite !id_left, id_right.
    apply idpath.
  Qed.

  Proposition mon_lassociator_lassociator'
              {w x y z : V}
    : mon_lassociator (w ⊗ x) y z
        · mon_lassociator w x (y ⊗ z)
        · w ⊗^{V}_{l} mon_rassociator x y z
      = mon_lassociator w x y ⊗^{V}_{r} z
      · mon_lassociator w (x ⊗ y) z.
  Proof.
     etrans. {
        apply maponpaths_2.
        apply mon_lassociator_lassociator.
      }
      rewrite <- (when_bifunctor_becomes_leftwhiskering V).
      rewrite ! assoc'.
      etrans. {
        do 2 apply maponpaths.
        apply pathsinv0, tensor_comp_id_l.
      }
      etrans. {
        do 2 apply maponpaths.
        apply maponpaths.
        apply mon_lassociator_rassociator.
      }
      rewrite tensor_id_id.
      rewrite id_right.
      apply maponpaths_2.
      apply (when_bifunctor_becomes_rightwhiskering V).
  Qed.

  Proposition mon_rassociator_rassociator
              {w x y z : V}
    : mon_rassociator w x (y ⊗ z)
      · mon_rassociator (w ⊗ x) y z
      =
      identity w #⊗ mon_rassociator x y z
      · mon_rassociator w (x ⊗ y) z
      · mon_rassociator w x y #⊗ identity z.
  Proof.
    refine (!(monoidal_pentagon_identity_inv V w x y z) @ _).
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite (bifunctor_rightid V).
    rewrite (bifunctor_leftid V).
    rewrite !id_left, id_right.
    apply idpath.
  Qed.

  Definition monoidal_left_tensor_data
             (x : V)
    : functor_data V V.
  Proof.
    use make_functor_data.
    - exact (λ y, x ⊗ y).
    - exact (λ y₁ y₂ f, identity x #⊗ f).
  Defined.

  Proposition is_functor_monoidal_left_tensor
              (x : V)
    : is_functor (monoidal_left_tensor_data x).
  Proof.
    split.
    - intros y ; cbn.
      apply tensor_id_id.
    - intros y₁ y₂ y₃ f g ; cbn.
      apply tensor_comp_id_l.
  Qed.

  Definition monoidal_left_tensor
             (x : V)
    : V ⟶ V.
  Proof.
    use make_functor.
    - exact (monoidal_left_tensor_data x).
    - exact (is_functor_monoidal_left_tensor x).
  Defined.

  Definition monoidal_right_tensor_data
             (y : V)
    : functor_data V V.
  Proof.
    use make_functor_data.
    - exact (λ x, x ⊗ y).
    - exact (λ x₁ x₂ f, f #⊗ identity y).
  Defined.

  Proposition is_functor_monoidal_right_tensor
              (y : V)
    : is_functor (monoidal_right_tensor_data y).
  Proof.
    split.
    - intros x ; cbn.
      apply tensor_id_id.
    - intros x₁ x₂ x₃ f g ; cbn.
      apply tensor_comp_id_r.
  Qed.

  Definition monoidal_right_tensor
             (y : V)
    : V ⟶ V.
  Proof.
    use make_functor.
    - exact (monoidal_right_tensor_data y).
    - exact (is_functor_monoidal_right_tensor y).
  Defined.
End MonoidalCatAccessors.

Definition monoidal_cat_tensor_data
           (V : monoidal_cat)
  : functor_data (category_binproduct V V) V.
Proof.
  use make_functor_data.
  - exact (λ x, pr1 x ⊗ pr2 x).
  - exact (λ x y f, pr1 f #⊗ pr2 f).
Defined.

Proposition is_functor_monoidal_cat_tensor
            (V : monoidal_cat)
  : is_functor (monoidal_cat_tensor_data V).
Proof.
  split.
  - intro x ; cbn.
    apply tensor_id_id.
  - intros x y z f g ; cbn.
    apply tensor_comp_mor.
Qed.

Definition monoidal_cat_tensor
           (V : monoidal_cat)
  : category_binproduct V V ⟶ V.
Proof.
  use make_functor.
  - exact (monoidal_cat_tensor_data V).
  - exact (is_functor_monoidal_cat_tensor V).
Defined.
