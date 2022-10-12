Require Import UniMath.MoreFoundations.Notations.

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

Definition leftunitor_data {C : category} (T : tensor C) (I : C) : UU :=
  ∏ (x : C), C⟦I ⊗_{T} x, x⟧.

Definition leftunitorinv_data {C : category} (T : tensor C) (I : C) : UU :=
  ∏ (x : C), C⟦x, I ⊗_{T} x⟧.

Definition rightunitor_data {C : category} (T : tensor C) (I : C) : UU :=
  ∏ (x : C), C⟦x ⊗_{T} I, x⟧.

Definition rightunitorinv_data {C : category} (T : tensor C) (I : C) : UU :=
  ∏ (x : C), C⟦x, x ⊗_{T} I⟧.

Definition associator_data {C : category} (T : tensor C) : UU :=
  ∏ (x y z : C), C ⟦(x ⊗_{T} y) ⊗_{T} z, x ⊗_{T} (y ⊗_{T} z)⟧.

Definition associatorinv_data {C : category} (T : tensor C) : UU :=
  ∏ (x y z : C), C ⟦x ⊗_{T} (y ⊗_{T} z), (x ⊗_{T} y) ⊗_{T} z⟧.

Definition monoidal_data (C : category): UU :=
    ∑ T : tensor C, ∑ I : C,
        (leftunitor_data T I) × (leftunitorinv_data T I) ×
          (rightunitor_data T I) × (rightunitorinv_data T I) ×
          (associator_data T) × (associatorinv_data T).

Definition make_monoidal_data {C : category} {T : tensor C} {I : C}
  (lu : leftunitor_data T I) (luinv : leftunitorinv_data T I)
  (ru : rightunitor_data T I) (ruinv : rightunitorinv_data T I)
  (α : associator_data T) (αinv : associatorinv_data T) : monoidal_data C
  := (T,,I,,lu,,luinv,,ru,,ruinv,,α,,αinv).

Definition monoidal_tensor {C : category} (MD : monoidal_data C) : tensor C := pr1 MD.
Coercion monoidal_tensor : monoidal_data >-> tensor.

Definition monoidal_unit {C : category} (MD : monoidal_data C) : C := pr12 MD.
Notation "I_{ MD }" := (monoidal_unit MD).

Definition monoidal_leftunitordata {C : category} (MD : monoidal_data C) : leftunitor_data MD I_{MD}
  := pr1 (pr22 MD).
Notation "lu_{ MD }" := (monoidal_leftunitordata MD).

Definition monoidal_leftunitorinvdata {C : category} (MD : monoidal_data C) : leftunitorinv_data MD I_{MD}
  := pr12 (pr22 MD).
Notation "luinv_{ MD }" := (monoidal_leftunitorinvdata MD).

Definition monoidal_rightunitordata {C : category} (MD : monoidal_data C) : rightunitor_data MD I_{MD}
  := pr122 (pr22 MD).
Notation "ru_{ MD }" := (monoidal_rightunitordata MD).

Definition monoidal_rightunitorinvdata {C : category} (MD : monoidal_data C) : rightunitorinv_data MD I_{MD}
  := pr1 (pr222 (pr22 MD)).
Notation "ruinv_{ MD }" := (monoidal_rightunitorinvdata MD).

Definition monoidal_associatordata {C : category} (MD : monoidal_data C) : associator_data MD
  := pr12 (pr222 (pr22 MD)).
Notation "α_{ MD }" := (monoidal_associatordata MD).

Definition monoidal_associatorinvdata {C : category} (MD : monoidal_data C) : associatorinv_data MD
  := pr22 (pr222 (pr22 MD)).
Notation "αinv_{ MD }" := (monoidal_associatorinvdata MD).

(** Axioms **)
Definition leftunitor_nat {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  I ⊗^{ T}_{l} f · lu y = lu x · f.

Definition leftunitorinv_nat {C : category} {T : tensor C} {I : C} (luinv : leftunitorinv_data T I) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  luinv x · I ⊗^{ T}_{l} f = f · luinv y.

Definition leftunitor_iso_law {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) (luinv : leftunitorinv_data T I) : UU :=
  ∏ (x : C), is_inverse_in_precat (lu x) (luinv x).

Definition leftunitor_law {C : category} {T : tensor C} {I : C} (lu : leftunitor_data T I) (luinv : leftunitorinv_data T I) : UU :=
  leftunitor_nat lu × leftunitor_iso_law lu luinv.

Definition leftunitorlaw_nat {C : category} {T : tensor C} {I : C} {lu : leftunitor_data T I} {luinv : leftunitorinv_data T I}
  (lul : leftunitor_law lu luinv) : leftunitor_nat lu := pr1 lul.

Definition leftunitorlaw_iso_law {C : category} {T : tensor C} {I : C} {lu : leftunitor_data T I} {luinv : leftunitorinv_data T I}
  (lul : leftunitor_law lu luinv) : leftunitor_iso_law lu luinv := pr2 lul.

Definition rightunitor_nat {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  f ⊗^{ T}_{r} I · ru y = ru x · f.

Definition rightunitorinv_nat {C : category} {T : tensor C} {I : C} (ruinv : rightunitorinv_data T I) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  ruinv x · f ⊗^{ T}_{r} I = f · ruinv y.

Definition rightunitor_iso_law {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) (ruinv : rightunitorinv_data T I) : UU :=
  ∏ (x : C), is_inverse_in_precat (ru x) (ruinv x).

Definition rightunitor_law {C : category} {T : tensor C} {I : C} (ru : rightunitor_data T I) (ruinv : rightunitorinv_data T I) : UU :=
  rightunitor_nat ru × rightunitor_iso_law ru ruinv.

Definition rightunitorlaw_nat {C : category} {T : tensor C} {I : C} {ru : rightunitor_data T I} {ruinv : rightunitorinv_data T I} (rul : rightunitor_law ru ruinv) : rightunitor_nat ru := pr1 rul.

Definition rightunitorlaw_iso_law {C : category} {T : tensor C} {I : C} {ru : rightunitor_data T I} {ruinv : rightunitorinv_data T I} (rul : rightunitor_law ru ruinv) : rightunitor_iso_law ru ruinv := pr2 rul.

Definition associator_nat_leftwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x y z z' : C) (h : C⟦z,z'⟧),
    (α x y z) · (x ⊗^{ T}_{l} (y ⊗^{ T}_{l} h)) = ((x ⊗_{ T} y) ⊗^{ T}_{l} h) · (α x y z').

Definition associator_nat_rightwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x x' y z : C) (f : C⟦x,x'⟧),
    (α x y z) · (f ⊗^{ T}_{r} (y ⊗_{ T} z)) = ((f ⊗^{ T}_{r} y) ⊗^{ T}_{r} z) · (α x' y z).

Definition associator_nat_leftrightwhisker {C : category} {T : tensor C} (α : associator_data T) : UU
  := ∏ (x y y' z : C) (g : C⟦y,y'⟧),
    (α x y z) · (x ⊗^{ T}_{l} (g ⊗^{ T}_{r} z)) = ((x ⊗^{ T}_{l} g) ⊗^{ T}_{r} z) · (α x y' z).

Lemma associator_nat1 {C : category} {T : tensor C} {α : associator_data T} (αnl : associator_nat_leftwhisker α)
  (αnr : associator_nat_rightwhisker α) (αnlr : associator_nat_leftrightwhisker α)
  {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
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

Lemma associator_nat2 {C : category} {T : tensor C} {α : associator_data T} (αnl : associator_nat_leftwhisker α)
  (αnr : associator_nat_rightwhisker α) (αnlr : associator_nat_leftrightwhisker α)
  {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
  (α x y z) · (f ⊗^{T} (g ⊗^{T} h)) = ((f ⊗^{T} g) ⊗^{T} h) · (α x' y' z').
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (associator_nat1 αnl αnr αnlr f g h).
Qed.

Definition associator_iso_law {C : category} {T : tensor C} (α : associator_data T) (αinv : associatorinv_data T) : UU
  := ∏ (x y z : C), is_inverse_in_precat (α x y z) (αinv x y z).

Definition associator_law {C : category} {T : tensor C} (α : associator_data T) (αinv : associatorinv_data T) : UU :=
  (associator_nat_leftwhisker α) × (associator_nat_rightwhisker α) ×
    (associator_nat_leftrightwhisker α) × (associator_iso_law α αinv).

Definition associatorlaw_natleft {C : category} {T : tensor C} {α : associator_data T} {αinv : associatorinv_data T}
  (αl : associator_law α αinv) : associator_nat_leftwhisker α := pr1 αl.
Definition associatorlaw_natright {C : category} {T : tensor C} {α : associator_data T} {αinv : associatorinv_data T}
  (αl : associator_law α αinv) : associator_nat_rightwhisker α := pr1 (pr2 αl).
Definition associatorlaw_natleftright {C : category} {T : tensor C} {α : associator_data T} {αinv : associatorinv_data T}
  (αl : associator_law α αinv) : associator_nat_leftrightwhisker α := pr1 (pr2 (pr2 αl)).
Definition associatorlaw_iso_law {C : category} {T : tensor C} {α : associator_data T} {αinv : associatorinv_data T}
  (αl : associator_law α αinv) : associator_iso_law α αinv := pr2 (pr2 (pr2 αl)).

Definition triangle_identity {C : category}
           {T : tensor C}
           {I : C}
           (lu : leftunitor_data T I)
           (ru : rightunitor_data T I)
           (α : associator_data T)
    := ∏ (x y : C), (α x I y) · (x ⊗^{T}_{l} (lu y)) = (ru x) ⊗^{T}_{r} y.

Definition pentagon_identity {C : category} {T : tensor C} (α : associator_data T) : UU :=
  ∏ (w x y z : C),
    ((α w x y) ⊗^{T}_{r} z) · (α w (x⊗_{T} y) z) · (w ⊗^{T}_{l} (α x y z)) = (α (w⊗_{T}x) y z) · (α w x (y ⊗_{T} z)).

Definition monoidal_laws {C : category} (MD : monoidal_data C) : UU :=
  (leftunitor_law lu_{MD} luinv_{MD}) × (rightunitor_law ru_{MD} ruinv_{MD}) × (associator_law α_{MD} αinv_{MD}) ×
    (triangle_identity lu_{MD} ru_{MD} α_{MD}) × (pentagon_identity α_{MD}).

Definition monoidal (C : category) : UU :=
  ∑ (MD : monoidal_data C), (monoidal_laws MD).

Definition monoidal_mondata {C : category} (M : monoidal C) : monoidal_data C := pr1 M.
Coercion monoidal_mondata : monoidal >-> monoidal_data.

Definition monoidal_monlaws {C : category} (M : monoidal C) : monoidal_laws M := pr2 M.

Definition monoidal_leftunitorlaw {C : category} (M : monoidal C) : leftunitor_law lu_{M} luinv_{M} := pr1 (monoidal_monlaws M).
Definition monoidal_leftunitornat {C : category} (M : monoidal C) : leftunitor_nat lu_{M} := leftunitorlaw_nat (monoidal_leftunitorlaw M).
Definition monoidal_leftunitorisolaw {C : category} (M : monoidal C) : leftunitor_iso_law lu_{M} luinv_{M} := leftunitorlaw_iso_law (monoidal_leftunitorlaw M).

Lemma monoidal_leftunitorinvnat {C : category} (M : monoidal C) : leftunitorinv_nat luinv_{M}.
Proof.
  intros x y f.
  apply (z_iso_inv_on_right _ _ _ (_,,_,,monoidal_leftunitorisolaw M x)).
  cbn.
  rewrite assoc.
  apply (z_iso_inv_on_left _ _ _ _ (_,,_,,monoidal_leftunitorisolaw M y)).
  apply pathsinv0, monoidal_leftunitornat.
Qed.

Definition monoidal_rightunitorlaw {C : category} (M : monoidal C) : rightunitor_law ru_{M} ruinv_{M} := pr12 (monoidal_monlaws M).
Definition monoidal_rightunitornat {C : category} (M : monoidal C) : rightunitor_nat ru_{M} := rightunitorlaw_nat (monoidal_rightunitorlaw M).

Definition monoidal_rightunitorisolaw {C : category} (M : monoidal C) : rightunitor_iso_law ru_{M} ruinv_{M} := rightunitorlaw_iso_law (monoidal_rightunitorlaw M).

Lemma monoidal_rightunitorinvnat {C : category} (M : monoidal C) : rightunitorinv_nat ruinv_{M}.
Proof.
  intros x y f.
  apply (z_iso_inv_on_right _ _ _ (_,,_,,monoidal_rightunitorisolaw M x)).
  cbn.
  rewrite assoc.
  apply (z_iso_inv_on_left _ _ _ _ (_,,_,,monoidal_rightunitorisolaw M y)).
  apply pathsinv0, monoidal_rightunitornat.
Qed.

Definition monoidal_associatorlaw {C : category} (M : monoidal C) : associator_law α_{M} αinv_{M} := pr122 (monoidal_monlaws M).
Definition monoidal_associatornatleft {C : category} (M : monoidal C) : associator_nat_leftwhisker α_{M} := associatorlaw_natleft (monoidal_associatorlaw M).
Definition monoidal_associatornatright {C : category} (M : monoidal C) : associator_nat_rightwhisker α_{M} := associatorlaw_natright (monoidal_associatorlaw M).
Definition monoidal_associatornatleftright {C : category} (M : monoidal C) : associator_nat_leftrightwhisker α_{M} := associatorlaw_natleftright (monoidal_associatorlaw M).
Definition monoidal_associatorisolaw {C : category} (M : monoidal C) : associator_iso_law α_{M} αinv_{M} := associatorlaw_iso_law (monoidal_associatorlaw M).

Definition monoidal_triangleidentity {C : category} (M : monoidal C) : triangle_identity lu_{M} ru_{M} α_{M} := pr1 (pr222 (monoidal_monlaws M)).
Definition monoidal_pentagonidentity {C : category} (M : monoidal C) : pentagon_identity α_{M} := pr2 (pr222 (monoidal_monlaws M)).

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
Lemma swap_nat_along_zisos {C : category} {x1 x2 y1 y2 : C}
  (p1 : z_iso x1 y1) (p2 : z_iso x2 y2) :
  ∏ (f: C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
    (pr1 p1) · g = f · (pr1 p2) -> g · (inv_from_z_iso p2) = (inv_from_z_iso p1) · f.
Proof.
  intros f g p.
  apply pathsinv0.
  apply z_iso_inv_on_right.
  rewrite assoc.
  apply z_iso_inv_on_left.
  apply p.
Qed.

Lemma leftunitor_nat_z_iso {C : category} (M : monoidal C):
  nat_z_iso (leftwhiskering_functor M (bifunctor_leftid M) (bifunctor_leftcomp M) I_{M}) (functor_identity C).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ x, lu_{M} x).
    + exact (λ x y f, monoidal_leftunitornat M x y f).
  - intro x. exists (luinv_{M} x).
    apply (monoidal_leftunitorisolaw M x).
Defined.

Definition rightunitor_nat_z_iso {C : category} (M : monoidal C) :
  nat_z_iso (rightwhiskering_functor M (bifunctor_rightid M) (bifunctor_rightcomp M) I_{M}) (functor_identity C).
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

Definition associatorinv_nat_leftwhisker {C : category} (M : monoidal C) :
  ∏ (x y z z' : C) (h : C⟦z,z'⟧),
    (x ⊗^{M}_{l} (y ⊗^{M}_{l} h)) · (αinv_{M} x y z') = (αinv_{M} x y z) · ((x ⊗_{M} y) ⊗^{M}_{l} h) .
Proof.
  intros x y z z' h.
  apply (swap_nat_along_zisos (z_iso_from_associator_iso M x y z) (z_iso_from_associator_iso M x y z')).
  apply monoidal_associatornatleft.
Qed.

Definition associatorinv_nat_rightwhisker {C : category} (M : monoidal C) :
  ∏ (x x' y z: C) (f : C⟦x,x'⟧),
    (f ⊗^{M}_{r} (y ⊗_{M} z)) · (αinv_{M} x' y z) = (αinv_{M} x y z) · ((f ⊗^{M}_{r} y) ⊗^{M}_{r} z).
Proof.
  intros x x' y z f.
  apply (swap_nat_along_zisos (z_iso_from_associator_iso M x y z) (z_iso_from_associator_iso M x' y z)).
  apply monoidal_associatornatright.
Qed.

Definition associatorinv_nat_leftrightwhisker {C : category} (M : monoidal C) :
  ∏ (x y y' z : C) (g : C⟦y,y'⟧),
    (x ⊗^{M}_{l} (g ⊗^{M}_{r} z)) · (αinv_{M} x y' z) = (αinv_{M} x y z) · ((x ⊗^{M}_{l} g) ⊗^{M}_{r} z).
Proof.
  intros x y y' z g.
  apply (swap_nat_along_zisos (z_iso_from_associator_iso M x y z) (z_iso_from_associator_iso M x y' z)).
  apply monoidal_associatornatleftright.
Qed.

Definition associatorinv_nat1 {C : category} (M : monoidal C)
  {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
  ((f ⊗^{M}_{r} (y ⊗_{M} z)) · (x' ⊗^{M}_{l} ((g ⊗^{M}_{r} z) · (y' ⊗^{M}_{l} h)))) · (αinv_{M} x' y' z') =
    (αinv_{M} x y z) · ((((f ⊗^{M}_{r} y) · (x' ⊗^{M}_{l} g))  ⊗^{M}_{r} z) · ((x' ⊗_{M} y') ⊗^{ M}_{l} h)).
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
  - exact (monoidal_associatornatleft M).
  - exact (monoidal_associatornatright M).
  - exact (monoidal_associatornatleftright M).
Qed.

Lemma associatorinv_nat2 {C : category} (M : monoidal C)
  {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
  (f ⊗^{M} (g ⊗^{M} h)) · (αinv_{M} x' y' z') = (αinv_{M} x y z) · ((f ⊗^{M} g) ⊗^{M} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  apply associatorinv_nat1.
Qed.

Lemma pentagon_identity_leftassociator {C : category} (M : monoidal C) (w x y z : C):
  w ⊗^{ M}_{l} (αinv_{M} x y z)
  · αinv_{M} w (x ⊗_{ M} y) z
  · αinv_{M} w x y ⊗^{ M}_{r} z =
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
    apply bifunctor_leftid.
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
  apply bifunctor_rightid.
Qed.

Module MonoidalNotations.
  Notation "I_{ M }" := (monoidal_unit M).
  Notation "lu^{ M }" := (monoidal_leftunitordata M).
  Notation "ru^{ M }" := (monoidal_rightunitordata M).
  Notation "α^{ M }" := (monoidal_associatordata M).
  Notation "lu^{ M }_{ x }" := (monoidal_leftunitordata M x ).
  Notation "ru^{ M }_{ x }" := ( monoidal_rightunitordata M x ).
  Notation "α^{ M }_{ x , y , z }" := (monoidal_associatordata M x y z).
  Notation "luinv^{ M }_{ x }" := (monoidal_leftunitorinvdata M x ).
  Notation "ruinv^{ M }_{ x }" := ( monoidal_rightunitorinvdata M x ).
  Notation "αinv^{ M }_{ x , y , z }" := (monoidal_associatorinvdata M x y z).
End MonoidalNotations.
