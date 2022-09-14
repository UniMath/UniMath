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
Definition actionop (C : category) : UU :=
  bifunctor V C C.
Identity Coercion actionopintobifunctor : actionop >-> bifunctor.

Definition aleftunitor_data {C : category} (A : actionop C) : UU :=
  ∏ (x : C), C⟦I_{Mon_V} ⊗_{A} x, x⟧.

Definition aleftunitorinv_data {C : category} (A : actionop C) : UU :=
  ∏ (x : C), C⟦x, I_{Mon_V} ⊗_{A} x⟧.

Definition convertor_data {C : category} (A : actionop C) : UU :=
  ∏ (v w : V) (x : C), C ⟦(v ⊗_{Mon_V} w) ⊗_{A} x, v ⊗_{A} (w ⊗_{A} x)⟧.

Definition convertorinv_data {C : category} (A : actionop C) : UU :=
  ∏ (v w : V) (x : C), C ⟦v ⊗_{A} (w ⊗_{A} x), (v ⊗_{Mon_V} w) ⊗_{A} x⟧.

Definition action_data (C : category) : UU :=
    ∑ A : actionop C,
        (aleftunitor_data A) × (aleftunitorinv_data A) ×
           (convertor_data A) × (convertorinv_data A).

Definition make_action_data {C : category} {A : actionop C}
  (alu : aleftunitor_data A) (aluinv : aleftunitorinv_data A)
  (χ : convertor_data A) (χinv : convertorinv_data A) : action_data C
  := (A,,alu,,aluinv,,χ,,χinv).

Definition monoidal_actionop {C : category} (AD : action_data C) : actionop C := pr1 AD.
Coercion monoidal_actionop : action_data >-> actionop.

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


(** Axioms **)
Definition aleftunitor_nat {C : category} {A : actionop C} (alu : aleftunitor_data A) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  I_{Mon_V} ⊗^{A}_{l} f · alu y = alu x · f.

Definition aleftunitorinv_nat {C : category} {A : actionop C} (aluinv : aleftunitorinv_data A) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  aluinv x · I_{Mon_V} ⊗^{A}_{l} f = f · aluinv y.

Definition aleftunitor_iso_law {C : category} {A : actionop C} (alu : aleftunitor_data A) (aluinv : aleftunitorinv_data A) : UU :=
  ∏ (x : C), is_inverse_in_precat (alu x) (aluinv x).

Definition aleftunitor_law {C : category} {A : actionop C} (alu : aleftunitor_data A) (aluinv : aleftunitorinv_data A) : UU :=
  aleftunitor_nat alu × aleftunitor_iso_law alu aluinv.

Definition aleftunitorlaw_nat {C : category} {A : actionop C} {alu : aleftunitor_data A} {aluinv : aleftunitorinv_data A}
  (alul : aleftunitor_law alu aluinv) : aleftunitor_nat alu := pr1 alul.

Definition aleftunitorlaw_iso_law {C : category} {A : actionop C} {alu : aleftunitor_data A} {aluinv : aleftunitorinv_data A}
  (alul : aleftunitor_law alu aluinv) : aleftunitor_iso_law alu aluinv := pr2 alul.

Definition convertor_nat_leftwhisker {C : category} {A : actionop C} (χ : convertor_data A) : UU
  := ∏ (v w : V) (z z' : C) (h : C⟦z,z'⟧),
    (χ v w z) · (v ⊗^{A}_{l} (w ⊗^{A}_{l} h)) = ((v ⊗_{Mon_V} w) ⊗^{A}_{l} h) · (χ v w z').

Definition convertor_nat_rightwhisker {C : category} {A : actionop C} (χ : convertor_data A) : UU
  := ∏ (v v' w : V) (z : C) (f : V⟦v,v'⟧),
    (χ v w z) · (f ⊗^{A}_{r} (w ⊗_{A} z)) = ((f ⊗^{Mon_V}_{r} w) ⊗^{A}_{r} z) · (χ v' w z).

Definition convertor_nat_leftrightwhisker {C : category} {A : actionop C} (χ : convertor_data A) : UU
  := ∏ (v w w' : V) (z : C) (g : V⟦w,w'⟧),
    (χ v w z) · (v ⊗^{A}_{l} (g ⊗^{A}_{r} z)) = ((v ⊗^{Mon_V}_{l} g) ⊗^{A}_{r} z) · (χ v w' z).

Lemma convertor_nat1 {C : category} {A : actionop C} {χ : convertor_data A} (χnl : convertor_nat_leftwhisker χ)
  (χnr : convertor_nat_rightwhisker χ) (χnlr : convertor_nat_leftrightwhisker χ)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (χ v w z) · ((f ⊗^{A}_{r} (w ⊗_{A} z)) · (v' ⊗^{A}_{l} ((g ⊗^{A}_{r} z) · (w' ⊗^{A}_{l} h)))) =
    (((f ⊗^{Mon_V}_{r} w) · (v' ⊗^{Mon_V}_{l} g))  ⊗^{A}_{r} z) · ((v' ⊗_{Mon_V} w') ⊗^{A}_{l} h) · (χ v' w' z').
Proof.
  rewrite assoc.
  rewrite χnr.
  rewrite assoc'.
  etrans. {
    apply cancel_precomposition.
    rewrite (bifunctor_leftcomp A).
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
  rewrite (bifunctor_rightcomp A).
  apply idpath.
Qed.

Lemma convertor_nat2 {C : category} {A : actionop C} {χ : convertor_data A} (χnl : convertor_nat_leftwhisker χ)
  (χnr : convertor_nat_rightwhisker χ) (χnlr : convertor_nat_leftrightwhisker χ)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (χ v w z) · (f ⊗^{A} (g ⊗^{A} h)) = ((f ⊗^{Mon_V} g) ⊗^{A} h) · (χ v' w' z').
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (convertor_nat1 χnl χnr χnlr f g h).
Qed.

Definition convertor_iso_law {C : category} {A : actionop C} (χ : convertor_data A) (χinv : convertorinv_data A) : UU
  := ∏ (v w : V) (z : C), is_inverse_in_precat (χ v w z) (χinv v w z).

Definition convertor_law {C : category} {A : actionop C} (χ : convertor_data A) (χinv : convertorinv_data A) : UU :=
  (convertor_nat_leftwhisker χ) × (convertor_nat_rightwhisker χ) ×
    (convertor_nat_leftrightwhisker χ) × (convertor_iso_law χ χinv).

Definition convertorlaw_natleft {C : category} {A : actionop C} {χ : convertor_data A} {χinv : convertorinv_data A}
  (χl : convertor_law χ χinv) : convertor_nat_leftwhisker χ := pr1 χl.
Definition convertorlaw_natright {C : category} {A : actionop C} {χ : convertor_data A} {χinv : convertorinv_data A}
  (χl : convertor_law χ χinv) : convertor_nat_rightwhisker χ := pr1 (pr2 χl).
Definition convertorlaw_natleftright {C : category} {A : actionop C} {χ : convertor_data A} {χinv : convertorinv_data A}
  (χl : convertor_law χ χinv) : convertor_nat_leftrightwhisker χ := pr1 (pr2 (pr2 χl)).
Definition convertorlaw_iso_law {C : category} {A : actionop C} {χ : convertor_data A} {χinv : convertorinv_data A}
  (χl : convertor_law χ χinv) : convertor_iso_law χ χinv := pr2 (pr2 (pr2 χl)).

Definition action_triangle_identity {C : category}
           {A : actionop C}
           (alu : aleftunitor_data A)
           (χ : convertor_data A)
    := ∏ (v : V) (y : C), (χ v I_{Mon_V} y) · (v ⊗^{A}_{l} (alu y)) = (ru_{Mon_V} v) ⊗^{A}_{r} y.

Definition action_pentagon_identity {C : category} {A : actionop C} (χ : convertor_data A) : UU :=
  ∏ (w v v' : V) (z : C),
    ((α_{Mon_V} w v v') ⊗^{A}_{r} z) · (χ w (v ⊗_{Mon_V} v') z) · (w ⊗^{A}_{l} (χ v v' z)) =
      (χ (w⊗_{Mon_V} v) v' z) · (χ w v (v' ⊗_{A} z)).

Definition action_laws {C : category} (AD : action_data C) : UU :=
  (aleftunitor_law alu_{AD} aluinv_{AD}) × (convertor_law χ_{AD} χinv_{AD}) ×
    (action_triangle_identity alu_{AD} χ_{AD}) × (action_pentagon_identity χ_{AD}).

Definition action (C : category) : UU :=
  ∑ (AD : action_data C), (action_laws AD).

Definition action_actiondata {C : category} (Act : action C) : action_data C := pr1 Act.
Coercion action_actiondata : action >-> action_data.

Definition action_monlaws {C : category} (Act : action C) : action_laws Act := pr2 Act.

Definition action_leftunitorlaw {C : category} (Act : action C) : aleftunitor_law alu_{Act} aluinv_{Act} := pr1 (action_monlaws Act).
Definition action_leftunitornat {C : category} (Act : action C) : aleftunitor_nat alu_{Act} := aleftunitorlaw_nat (action_leftunitorlaw Act).
Definition action_leftunitorisolaw {C : category} (Act : action C) : aleftunitor_iso_law alu_{Act} aluinv_{Act} := aleftunitorlaw_iso_law (action_leftunitorlaw Act).

Lemma action_leftunitorinvnat {C : category} (Act : action C) : aleftunitorinv_nat aluinv_{Act}.
Proof.
  intros x y f.
  apply (z_iso_inv_on_right _ _ _ (_,,_,,action_leftunitorisolaw Act x)).
  cbn.
  rewrite assoc.
  apply (z_iso_inv_on_left _ _ _ _ (_,,_,,action_leftunitorisolaw Act y)).
  apply pathsinv0, action_leftunitornat.
Qed.

Definition action_convertorlaw {C : category} (Act : action C) : convertor_law χ_{Act} χinv_{Act} := pr12 (action_monlaws Act).
Definition action_convertornatleft {C : category} (Act : action C) : convertor_nat_leftwhisker χ_{Act} := convertorlaw_natleft (action_convertorlaw Act).
Definition action_convertornatright {C : category} (Act : action C) : convertor_nat_rightwhisker χ_{Act} := convertorlaw_natright (action_convertorlaw Act).
Definition action_convertornatleftright {C : category} (Act : action C) : convertor_nat_leftrightwhisker χ_{Act} := convertorlaw_natleftright (action_convertorlaw Act).
Definition action_convertorisolaw {C : category} (Act : action C) : convertor_iso_law χ_{Act} χinv_{Act} := convertorlaw_iso_law (action_convertorlaw Act).

Definition action_triangleidentity {C : category} (Act : action C) : action_triangle_identity alu_{Act} χ_{Act} := pr1 (pr22 (action_monlaws Act)).
Definition action_pentagonidentity {C : category} (Act : action C) : action_pentagon_identity χ_{Act} := pr2 (pr22 (action_monlaws Act)).

Lemma isaprop_action_laws {C : category} (AD : action_data C)
  : isaprop (action_laws AD).
Proof.
  repeat (apply isapropdirprod)
  ; repeat (apply impred ; intro)
  ; repeat (try apply C)
  ; repeat (apply isaprop_is_inverse_in_precat).
Qed.

(** Some additional data and properties which one deduces from action categories **)

Lemma aleftunitor_nat_z_iso {C : category} (Act : action C):
  nat_z_iso (leftwhiskering_functor Act (bifunctor_leftid Act) (bifunctor_leftcomp Act) I_{Mon_V}) (functor_identity C).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ x, alu_{Act} x).
    + exact (λ x y f, action_leftunitornat Act x y f).
  - intro x. exists (aluinv_{Act} x).
    apply (action_leftunitorisolaw Act x).
Defined.

Definition z_iso_from_convertor_iso
  {C : category} (Act : action C) (v w : V) (x : C)
  : z_iso ((v ⊗_{Mon_V} w) ⊗_{Act} x) (v ⊗_{Act} (w ⊗_{Act} x))
  := make_z_iso
       (χ_{Act} v w x)
       (χinv_{Act} v w x)
       (action_convertorisolaw Act v w x).

Definition convertorinv_nat_leftwhisker {C : category} (Act : action C) :
  ∏ (v w : V) (z z' : C) (h : C⟦z,z'⟧),
    (v ⊗^{Act}_{l} (w ⊗^{Act}_{l} h)) · (χinv_{Act} v w z') = (χinv_{Act} v w z) · ((v ⊗_{Mon_V} w) ⊗^{Act}_{l} h) .
Proof.
  intros v w z z' h.
  apply (swap_nat_along_zisos (z_iso_from_convertor_iso Act v w z) (z_iso_from_convertor_iso Act v w z')).
  apply action_convertornatleft.
Qed.

Definition convertorinv_nat_rightwhisker {C : category} (Act : action C) :
  ∏ (v v' w : V) (z: C) (f : V⟦v,v'⟧),
    (f ⊗^{Act}_{r} (w ⊗_{Act} z)) · (χinv_{Act} v' w z) = (χinv_{Act} v w z) · ((f ⊗^{Mon_V}_{r} w) ⊗^{Act}_{r} z).
Proof.
  intros v v' w z f.
  apply (swap_nat_along_zisos (z_iso_from_convertor_iso Act v w z) (z_iso_from_convertor_iso Act v' w z)).
  apply action_convertornatright.
Qed.

Definition convertorinv_nat_leftrightwhisker {C : category} (Act : action C) :
  ∏ (v w w' : V) (z : C) (g : V⟦w,w'⟧),
    (v ⊗^{Act}_{l} (g ⊗^{Act}_{r} z)) · (χinv_{Act} v w' z) = (χinv_{Act} v w z) · ((v ⊗^{Mon_V}_{l} g) ⊗^{Act}_{r} z).
Proof.
  intros v w w' z g.
  apply (swap_nat_along_zisos (z_iso_from_convertor_iso Act v w z) (z_iso_from_convertor_iso Act v w' z)).
  apply action_convertornatleftright.
Qed.

Definition convertorinv_nat1 {C : category} (Act : action C)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  ((f ⊗^{Act}_{r} (w ⊗_{Act} z)) · (v' ⊗^{Act}_{l} ((g ⊗^{Act}_{r} z) · (w' ⊗^{Act}_{l} h)))) · (χinv_{Act} v' w' z') =
    (χinv_{Act} v w z) · ((((f ⊗^{Mon_V}_{r} w) · (v' ⊗^{Mon_V}_{l} g)) ⊗^{Act}_{r} z) · ((v' ⊗_{Mon_V} w') ⊗^{ Act}_{l} h)).
Proof.
  apply (swap_nat_along_zisos
           (z_iso_from_convertor_iso Act v w z)
           (z_iso_from_convertor_iso Act v' w' z')
        ).
  unfold z_iso_from_convertor_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  unfold pr1.
  apply convertor_nat1.
  - exact (action_convertornatleft Act).
  - exact (action_convertornatright Act).
  - exact (action_convertornatleftright Act).
Qed.

Lemma convertorinv_nat2 {C : category} (Act : action C)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (f ⊗^{Act} (g ⊗^{Act} h)) · (χinv_{Act} v' w' z') = (χinv_{Act} v w z) · ((f ⊗^{Mon_V} g) ⊗^{Act} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  apply convertorinv_nat1.
Qed.

Lemma pentagon_identity_leftconvertor {C : category} (Act : action C) (w v u : V) (z : C):
  w ⊗^{ Act}_{l} (χinv_{Act} v u z)
  · χinv_{Act} w (v ⊗_{Mon_V} u) z
  · αinv_{Mon_V} w v u ⊗^{Act}_{r} z =
    χinv_{Act} w v (u ⊗_{Act} z)
  · χinv_{Act} (w ⊗_{Mon_V} v) u z.
Proof.
  apply pathsinv0.
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_convertor_iso Act _ _ _)).
  unfold z_iso_from_convertor_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  etrans. { apply (pathsinv0 (id_right _)). }
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_convertor_iso Act _ _ _)).
  cbn.
  apply pathsinv0.
  etrans. {
   rewrite assoc.
   apply cancel_postcomposition.
   apply (pathsinv0 (action_pentagonidentity Act w v u z)).
  }
  etrans. {
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (pathsinv0 (bifunctor_leftcomp Act _ _ _ _ _ _)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply cancel_precomposition.
    apply maponpaths.
    apply (pr2 (z_iso_from_convertor_iso Act v u z)).
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
    apply (pr2 (z_iso_from_convertor_iso Act w (v⊗_{Mon_V}u) z)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply id_right.
  }
  etrans. {
    apply (pathsinv0 (bifunctor_rightcomp Act _ _ _ _ _ _)).
  }
  etrans. {
    apply maponpaths.
    apply (pr2 (pr2 (z_iso_from_associator_iso Mon_V w v u))).
  }
  apply bifunctor_rightid.
Qed.

Module ActionNotations.
  Notation "alu^{ Act }" := (action_leftunitordata Act).
  Notation "χ^{ Act }" := (action_convertordata Act).
  Notation "alu^{ Act }_{ x }" := (action_leftunitordata Act x ).
  Notation "χ^{ Act }_{ x , y , z }" := (action_convertordata Act x y z).
  Notation "aluinv^{ Act }_{ x }" := (action_leftunitorinvdata Act x ).
  Notation "χinv^{ Act }_{ x , y , z }" := (action_convertorinvdata Act x y z).
End ActionNotations.
