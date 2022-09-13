(** the concept of left action of a monoidal category on a category *)

Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Local Open Scope cat.

Import BifunctorNotations.

Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)

(** Data **)
Definition action (C : category) : UU :=
  bifunctor V C C.
Identity Coercion actionintobifunctor : action >-> bifunctor.

Definition aleftunitor_data {C : category} (A : action C) : UU :=
  ∏ (x : C), C⟦I_{Mon_V} ⊗_{A} x, x⟧.

Definition aleftunitorinv_data {C : category} (A : action C) : UU :=
  ∏ (x : C), C⟦x, I_{Mon_V} ⊗_{A} x⟧.

Definition convertor_data {C : category} (A : action C) : UU :=
  ∏ (v w : V) (x : C), C ⟦(v ⊗_{Mon_V} w) ⊗_{A} x, v ⊗_{A} (w ⊗_{A} x)⟧.

Definition convertorinv_data {C : category} (A : action C) : UU :=
  ∏ (v w : V) (x : C), C ⟦v ⊗_{A} (w ⊗_{A} x), (v ⊗_{Mon_V} w) ⊗_{A} x⟧.

Definition action_data (C : category) : UU :=
    ∑ A : action C,
        (aleftunitor_data A) × (aleftunitorinv_data A) ×
           (convertor_data A) × (convertorinv_data A).

Definition make_action_data {C : category} {A : action C}
  (alu : aleftunitor_data A) (aluinv : aleftunitorinv_data A)
  (χ : convertor_data A) (χinv : convertorinv_data A) : action_data C
  := (A,,alu,,aluinv,,χ,,χinv).

Definition monoidal_action {C : category} (AD : action_data C) : action C := pr1 AD.
Coercion monoidal_action : action_data >-> action.

Definition action_leftunitordata {C : category} (AD : action_data C) : aleftunitor_data AD
  := pr1 (pr2 AD).
Notation "alu_{ AD }" := (action_leftunitordata AD).

Definition action_leftunitorinvdata {C : category} (AD : action_data C) : aleftunitorinv_data AD
  := pr12 (pr2 AD).
Notation "aluinv_{ AD }" := (action_leftunitorinvdata AD).

Definition action_convertordata {C : category} (AD : action_data C) : convertor_data AD
  := pr12 (pr2 (pr2 AD)).
Notation "χ_{ AD }" := (action_convertordata AD).

Definition action_convertorinvdata {C : category} (AD : action_data C) : convertorinv_data AD
  := pr22 (pr2 (pr2 AD)).
Notation "χinv_{ AD }" := (action_convertorinvdata AD).

Definition monoidal_associatorinvdata {C : category} (MD : monoidal_data C) : associatorinv_data MD
  := pr22 (pr222 (pr22 MD)).
Notation "αinv_{ MD }" := (monoidal_associatorinvdata MD).

(** Axioms **)
Definition aleftunitor_nat {C : category} {A : action C} (alu : aleftunitor_data A) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  I_{Mon_V} ⊗^{A}_{l} f · alu y = alu x · f.

Definition aleftunitorinv_nat {C : category} {A : action C} (aluinv : aleftunitorinv_data A) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  aluinv x · I_{Mon_V} ⊗^{A}_{l} f = f · aluinv y.

Definition aleftunitor_iso_law {C : category} {A : action C} (alu : aleftunitor_data A) (aluinv : aleftunitorinv_data A) : UU :=
  ∏ (x : C), is_inverse_in_precat (alu x) (aluinv x).

Definition aleftunitor_law {C : category} {A : action C} (alu : aleftunitor_data A) (aluinv : aleftunitorinv_data A) : UU :=
  aleftunitor_nat alu × aleftunitor_iso_law alu aluinv.

Definition aleftunitorlaw_nat {C : category} {A : action C} {alu : aleftunitor_data A} {aluinv : aleftunitorinv_data A}
  (alul : aleftunitor_law alu aluinv) : aleftunitor_nat alu := pr1 alul.

Definition aleftunitorlaw_iso_law {C : category} {A : action C} {alu : aleftunitor_data A} {aluinv : aleftunitorinv_data A}
  (alul : aleftunitor_law alu aluinv) : aleftunitor_iso_law alu aluinv := pr2 alul.

Definition convertor_nat_leftwhisker {C : category} {A : action C} (χ : convertor_data A) : UU
  := ∏ (v w : V) (z z' : C) (h : C⟦z,z'⟧),
    (χ v w z) · (v ⊗^{A}_{l} (w ⊗^{A}_{l} h)) = ((v ⊗_{Mon_V} w) ⊗^{A}_{l} h) · (χ v w z').

Definition convertor_nat_rightwhisker {C : category} {A : action C} (χ : convertor_data A) : UU
  := ∏ (v v' w : V) (z : C) (f : V⟦v,v'⟧),
    (χ v w z) · (f ⊗^{A}_{r} (w ⊗_{A} z)) = ((f ⊗^{Mon_V}_{r} w) ⊗^{A}_{r} z) · (χ v' w z).

Definition convertor_nat_leftrightwhisker {C : category} {A : action C} (χ : convertor_data A) : UU
  := ∏ (v w w' : V) (z : C) (g : V⟦w,w'⟧),
    (χ v w z) · (v ⊗^{A}_{l} (g ⊗^{A}_{r} z)) = ((v ⊗^{Mon_V}_{l} g) ⊗^{A}_{r} z) · (χ v w' z).

Lemma convertor_nat1 {C : category} {A : action C} {χ : convertor_data A} (χnl : convertor_nat_leftwhisker χ)
  (χnr : convertor_nat_rightwhisker χ) (χnlr : convertor_nat_leftrightwhisker χ)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (χ v w z) · ((f ⊗^{A}_{r} (w ⊗_{A} z)) · (v' ⊗^{A}_{l} ((g ⊗^{A}_{r} z) · (w' ⊗^{A}_{l} h)))) =
    (((f ⊗^{Mon_V}_{r} w) · (v' ⊗^{Mon_V}_{l} g))  ⊗^{A}_{r} z) · ((v' ⊗_{Mon_V} w') ⊗^{A}_{l} h) · (χ v' w' z').
Proof.
  (* TODO
  rewrite assoc.
  rewrite χnr.
  rewrite assoc'.
  etrans. {
    apply cancel_precomposition.
    rewrite (bifunctor_leftcomp T).
    rewrite assoc.
    rewrite χnlr.
    apply idpath.
  }

  etrans. {
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply χnl.
  }
  rewrite assoc.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0.
  rewrite bifunctor_rightcomp.
  apply idpath.
Qed.*)
  Admitted.

Lemma convertor_nat2 {C : category} {A : action C} {χ : convertor_data A} (χnl : convertor_nat_leftwhisker χ)
  (χnr : convertor_nat_rightwhisker χ) (χnlr : convertor_nat_leftrightwhisker χ)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (χ v w z) · (f ⊗^{A} (g ⊗^{A} h)) = ((f ⊗^{Mon_V} g) ⊗^{A} h) · (χ v' w' z').
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (convertor_nat1 χnl χnr χnlr f g h).
Qed.

(* TODO
Definition convertor_iso_law {C : category} {T : tensor C} (χ : convertor_data T) (χinv : convertorinv_data T) : UU
  := ∏ (x y z : C), is_inverse_in_precat (χ x y z) (χinv x y z).

Definition convertor_law {C : category} {T : tensor C} (χ : convertor_data T) (χinv : convertorinv_data T) : UU :=
  (convertor_nat_leftwhisker χ) × (convertor_nat_rightwhisker χ) ×
    (convertor_nat_leftrightwhisker χ) × (convertor_iso_law χ χinv).

Definition convertorlaw_natleft {C : category} {T : tensor C} {χ : convertor_data T} {χinv : convertorinv_data T}
  (χl : convertor_law χ χinv) : convertor_nat_leftwhisker χ := pr1 χl.
Definition convertorlaw_natright {C : category} {T : tensor C} {χ : convertor_data T} {χinv : convertorinv_data T}
  (χl : convertor_law χ χinv) : convertor_nat_rightwhisker χ := pr1 (pr2 χl).
Definition convertorlaw_natleftright {C : category} {T : tensor C} {χ : convertor_data T} {χinv : convertorinv_data T}
  (χl : convertor_law χ χinv) : convertor_nat_leftrightwhisker χ := pr1 (pr2 (pr2 χl)).
Definition convertorlaw_iso_law {C : category} {T : tensor C} {χ : convertor_data T} {χinv : convertorinv_data T}
  (χl : convertor_law χ χinv) : convertor_iso_law χ χinv := pr2 (pr2 (pr2 χl)).
*)
Definition atriangle_identity {C : category}
           {A : action C}
           (alu : aleftunitor_data A)
           (χ : convertor_data A)
    := ∏ (v : V) (y : C), (χ v I_{Mon_V} y) · (v ⊗^{A}_{l} (alu y)) = (ru_{Mon_V} v) ⊗^{A}_{r} y.

Definition pentagon_identity {C : category} {A : action C} (χ : convertor_data A) : UU :=
  ∏ (w v v' : V) (z : C),
    ((α_{Mon_V} w v v') ⊗^{A}_{r} z) · (χ w (v ⊗_{Mon_V} v') z) · (w ⊗^{A}_{l} (χ v v' z)) =
      (χ (w⊗_{Mon_V} v) v' z) · (χ w v (v' ⊗_{A} z)).

(* TODO

Definition monoidal_laws {C : category} (MD : monoidal_data C) : UU :=
  (leftunitor_law lu_{MD} luinv_{MD}) × (rightunitor_law ru_{MD} ruinv_{MD}) × (convertor_law χ_{MD} χinv_{MD}) ×
    (triangle_identity lu_{MD} ru_{MD} χ_{MD}) × (pentagon_identity χ_{MD}).

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

Definition monoidal_convertorlaw {C : category} (M : monoidal C) : convertor_law χ_{M} χinv_{M} := pr122 (monoidal_monlaws M).
Definition monoidal_convertornatleft {C : category} (M : monoidal C) : convertor_nat_leftwhisker χ_{M} := convertorlaw_natleft (monoidal_convertorlaw M).
Definition monoidal_convertornatright {C : category} (M : monoidal C) : convertor_nat_rightwhisker χ_{M} := convertorlaw_natright (monoidal_convertorlaw M).
Definition monoidal_convertornatleftright {C : category} (M : monoidal C) : convertor_nat_leftrightwhisker χ_{M} := convertorlaw_natleftright (monoidal_convertorlaw M).
Definition monoidal_convertorisolaw {C : category} (M : monoidal C) : convertor_iso_law χ_{M} χinv_{M} := convertorlaw_iso_law (monoidal_convertorlaw M).

Definition monoidal_triangleidentity {C : category} (M : monoidal C) : triangle_identity lu_{M} ru_{M} χ_{M} := pr1 (pr222 (monoidal_monlaws M)).
Definition monoidal_pentagonidentity {C : category} (M : monoidal C) : pentagon_identity χ_{M} := pr2 (pr222 (monoidal_monlaws M)).

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

Definition z_iso_from_convertor_iso
  {C : category} (M : monoidal C) (x y z : C)
  : z_iso ((x ⊗_{ M} y) ⊗_{ M} z) (x ⊗_{ M} (y ⊗_{ M} z))
  := make_z_iso
       (χ_{M} x y z)
       (χinv_{M} x y z)
       (monoidal_convertorisolaw M x y z).

Definition convertorinv_nat_leftwhisker {C : category} (M : monoidal C) :
  ∏ (x y z z' : C) (h : C⟦z,z'⟧),
    (x ⊗^{M}_{l} (y ⊗^{M}_{l} h)) · (χinv_{M} x y z') = (χinv_{M} x y z) · ((x ⊗_{M} y) ⊗^{M}_{l} h) .
Proof.
  intros x y z z' h.
  apply (swap_nat_along_zisos (z_iso_from_convertor_iso M x y z) (z_iso_from_convertor_iso M x y z')).
  apply monoidal_convertornatleft.
Qed.

Definition convertorinv_nat_rightwhisker {C : category} (M : monoidal C) :
  ∏ (x x' y z: C) (f : C⟦x,x'⟧),
    (f ⊗^{M}_{r} (y ⊗_{M} z)) · (χinv_{M} x' y z) = (χinv_{M} x y z) · ((f ⊗^{M}_{r} y) ⊗^{M}_{r} z).
Proof.
  intros x x' y z f.
  apply (swap_nat_along_zisos (z_iso_from_convertor_iso M x y z) (z_iso_from_convertor_iso M x' y z)).
  apply monoidal_convertornatright.
Qed.

Definition convertorinv_nat_leftrightwhisker {C : category} (M : monoidal C) :
  ∏ (x y y' z : C) (g : C⟦y,y'⟧),
    (x ⊗^{M}_{l} (g ⊗^{M}_{r} z)) · (χinv_{M} x y' z) = (χinv_{M} x y z) · ((x ⊗^{M}_{l} g) ⊗^{M}_{r} z).
Proof.
  intros x y y' z g.
  apply (swap_nat_along_zisos (z_iso_from_convertor_iso M x y z) (z_iso_from_convertor_iso M x y' z)).
  apply monoidal_convertornatleftright.
Qed.

Definition convertorinv_nat1 {C : category} (M : monoidal C)
  {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
  ((f ⊗^{M}_{r} (y ⊗_{M} z)) · (x' ⊗^{M}_{l} ((g ⊗^{M}_{r} z) · (y' ⊗^{M}_{l} h)))) · (χinv_{M} x' y' z') =
    (χinv_{M} x y z) · ((((f ⊗^{M}_{r} y) · (x' ⊗^{M}_{l} g))  ⊗^{M}_{r} z) · ((x' ⊗_{M} y') ⊗^{ M}_{l} h)).
Proof.
  apply (swap_nat_along_zisos
           (z_iso_from_convertor_iso M x y z)
           (z_iso_from_convertor_iso M x' y' z')
        ).
  unfold z_iso_from_convertor_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  unfold pr1.
  apply convertor_nat1.
  - exact (monoidal_convertornatleft M).
  - exact (monoidal_convertornatright M).
  - exact (monoidal_convertornatleftright M).
Qed.

Lemma convertorinv_nat2 {C : category} (M : monoidal C)
  {x x' y y' z z' : C} (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧) :
  (f ⊗^{M} (g ⊗^{M} h)) · (χinv_{M} x' y' z') = (χinv_{M} x y z) · ((f ⊗^{M} g) ⊗^{M} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  apply convertorinv_nat1.
Qed.

Lemma pentagon_identity_leftconvertor {C : category} (M : monoidal C) (w x y z : C):
  w ⊗^{ M}_{l} (χinv_{M} x y z)
  · χinv_{M} w (x ⊗_{ M} y) z
  · χinv_{M} w x y ⊗^{ M}_{r} z =
    χinv_{M} w x (y ⊗_{ M} z)
  · χinv_{M} (w ⊗_{ M} x) y z.
Proof.
  apply pathsinv0.
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_convertor_iso M _ _ _)).
  unfold z_iso_from_convertor_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  etrans. { apply (pathsinv0 (id_right _)). }
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_convertor_iso M _ _ _)).
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
    apply (pr2 (z_iso_from_convertor_iso M x y z)).
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
    apply (pr2 (z_iso_from_convertor_iso M w (x⊗_{M}y) z)).
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
    apply (pr2 (pr2 (z_iso_from_convertor_iso M w x y))).
  }
  apply bifunctor_rightid.
Qed.
*)
Module MonoidalNotations.
  Notation "alu^{ M }" := (action_leftunitordata M).
  Notation "χ^{ M }" := (action_convertordata M).
  Notation "alu^{ M }_{ x }" := (action_leftunitordata M x ).
  Notation "χ^{ M }_{ x , y , z }" := (action_convertordata M x y z).
  Notation "aluinv^{ M }_{ x }" := (action_leftunitorinvdata M x ).
  Notation "χinv^{ M }_{ x , y , z }" := (action_convertorinvdata M x y z).
End MonoidalNotations.
