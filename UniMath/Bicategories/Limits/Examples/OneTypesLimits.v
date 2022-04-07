(*********************************************************************************

 Limits of 1-types

 Contents:
 1. Final object
 2. Products
 3. Pullbacks
 4. Inserters
 5. Equifiers

 *********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.Equifiers.

Local Open Scope cat.

(**
 1. Final object
 *)

(** MOVE????*)
Definition isofhlevel_unit n : isofhlevel n unit
  := isofhlevelcontr n iscontrunit.

Definition unit_one_type : one_types
  := (unit,, isofhlevel_unit 3).

Definition bifinal_one_types
  : is_bifinal unit_one_type.
Proof.
  use make_is_bifinal.
  - exact (λ _ _, tt).
  - exact (λ _ _ _ _, pr1 (isapropunit _ _)).
  - intros Y f g α β.
    cbn in *.
    apply funextsec ; intro z.
    unfold homotsec in α,β.
    apply isasetunit.
Defined.

(**
 2. Products of 1-types
 *)
Definition one_types_binprod_cone
           (X Y : one_types)
  : binprod_cone X Y.
Proof.
  use make_binprod_cone.
  - use make_one_type.
    + exact (pr1 X × pr1 Y).
    + apply isofhleveldirprod.
      * exact (pr2 X).
      * exact (pr2 Y).
  - exact pr1.
  - exact pr2.
Defined.

Section OneTypesBinprodUMP.
  Context (X Y : one_types).

  Definition binprod_ump_1_one_types
    : binprod_ump_1 (one_types_binprod_cone X Y).
  Proof.
    intro q.
    use make_binprod_1cell.
    - exact (λ x, binprod_cone_pr1 q x ,, binprod_cone_pr2 q x).
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition binprod_ump_2_cell_one_types
    : has_binprod_ump_2_cell (one_types_binprod_cone X Y)
    := λ q f g p₁ p₂ x, pathsdirprod (p₁ x) (p₂ x).

  Definition binprod_ump_2_cell_pr1_one_types
    : has_binprod_ump_2_cell_pr1
        (one_types_binprod_cone X Y)
        binprod_ump_2_cell_one_types.
  Proof.
    intros q f g p₁ p₂.
    use funextsec.
    intro x.
    apply maponpaths_pr1_pathsdirprod.
  Qed.

  Definition binprod_ump_2_cell_pr2_one_types
    : has_binprod_ump_2_cell_pr2
        (one_types_binprod_cone X Y)
        binprod_ump_2_cell_one_types.
  Proof.
    intros q f g p₁ p₂.
    use funextsec.
    intro x.
    apply maponpaths_pr2_pathsdirprod.
  Qed.

  Definition binprod_ump_2_cell_unique_one_types
    : has_binprod_ump_2_cell_unique (one_types_binprod_cone X Y).
  Proof.
    intros q f g p₁ p₂ φ₁ φ₂ φ₁pr1 φ₁pr2 φ₂pr1 φ₂pr2.
    use funextsec.
    intro x.
    refine (pathsdirprod_eta _ @ _ @ !(pathsdirprod_eta _)).
    pose (eqtohomot φ₁pr1 x @ !(eqtohomot φ₂pr1 x)) as r₁.
    pose (eqtohomot φ₁pr2 x @ !(eqtohomot φ₂pr2 x)) as r₂.
    cbn in r₁, r₂ ; unfold homotfun in *.
    etrans.
    {
      apply maponpaths.
      exact r₂.
    }
    apply maponpaths_2.
    exact r₁.
  Qed.

  Definition has_binprod_ump_one_types
    : has_binprod_ump (one_types_binprod_cone X Y).
  Proof.
    use make_binprod_ump.
    - exact binprod_ump_1_one_types.
    - exact binprod_ump_2_cell_one_types.
    - exact binprod_ump_2_cell_pr1_one_types.
    - exact binprod_ump_2_cell_pr2_one_types.
    - exact binprod_ump_2_cell_unique_one_types.
  Defined.
End OneTypesBinprodUMP.

Definition has_binprod_one_types
  : has_binprod one_types.
Proof.
  intros X Y ; cbn in *.
  simple refine (_ ,, _).
  - exact (one_types_binprod_cone X Y).
  - exact (has_binprod_ump_one_types X Y).
Defined.

(**
 3. Pullbacks
 *)
Definition one_types_pb_cone
           {X Y Z : one_types}
           (f : X --> Z)
           (g : Y --> Z)
  : pb_cone f g.
Proof.
  use make_pb_cone.
  - exact (hfp_HLevel 3 f g).
  - exact (hfpg f g).
  - exact (hfpg' f g).
  - use make_invertible_2cell.
    + exact (λ x, !(commhfp f g x)).
    + apply one_type_2cell_iso.
Defined.

Section OneTypesPb.
  Context {X Y Z : one_types}
          (f : X --> Z)
          (g : Y --> Z).

  Definition one_types_pb_ump_1
    : pb_ump_1 (one_types_pb_cone f g).
  Proof.
    intro q.
    use make_pb_1cell.
    - exact (λ x, (pb_cone_pr1 q x ,, pb_cone_pr2 q x) ,, !(pr1 (pb_cone_cell q) x)).
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
    - abstract
        (use funextsec ;
         intro x ; cbn ;
         unfold homotcomp, homotfun, invhomot ;
         cbn ;
         rewrite !pathscomp0rid ;
         apply pathsinv0inv0).
  Defined.

  Definition one_types_pb_ump_2
    : pb_ump_2 (one_types_pb_cone f g).
  Proof.
    intros W φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use funextsec ; intro x ;
         use homot_hfp_one_type ;
         [ apply Z
         | exact (eqtohomot (pr12 τ₁) x @ !(eqtohomot (pr12 τ₂) x))
         | exact (eqtohomot (pr22 τ₁) x @ !(eqtohomot (pr22 τ₂) x)) ]).
    - simple refine (_ ,, _).
      + intro x.
        use path_hfp.
        * exact (α x).
        * exact (β x).
        * abstract
            (pose (eqtohomot r x) as p ;
             cbn in p ;
             unfold homotcomp, funhomotsec, homotfun in p ;
             cbn in p ;
             rewrite !pathscomp0rid in p ;
             use hornRotation_lr ;
             rewrite !path_assoc ;
             refine (_ @ maponpaths (λ z, z @ _) (!p)) ;
             rewrite <- !path_assoc ;
             rewrite pathsinv0l ;
             rewrite pathscomp0rid ;
             apply idpath).
      + split.
        * abstract
            (use funextsec ; intro x ;
             apply maponpaths_hfpg_path_hfp).
        * abstract
            (use funextsec ; intro x ;
             apply maponpaths_hfpg'_path_hfp).
  Defined.
End OneTypesPb.

Definition one_types_has_pb
  : has_pb one_types.
Proof.
  intros X Y Z f g.
  simple refine (_ ,, _ ,, _).
  - exact (one_types_pb_cone f g).
  - exact (one_types_pb_ump_1 f g).
  - exact (one_types_pb_ump_2 f g).
Defined.

(**
 4. Inserters
 *)
Definition inserter_type
           {X Y : UU}
           (f g : X → Y)
  : UU
  := ∑ (x : X), f x = g x.

Definition inserter_type_pr1
           {X Y : UU}
           (f g : X → Y)
  : inserter_type f g → X
  := pr1.

Definition inserter_type_path
           {X Y : UU}
           (f g : X → Y)
           (x : inserter_type f g)
  : f (inserter_type_pr1 f g x) = g (inserter_type_pr1 f g x)
  := pr2 x.

Definition isofhlevel_inserter_help
           {n : nat}
           {X Y : UU}
           (HX : isofhlevel n X)
           (HY : isofhlevel (S n) Y)
           (f g : X → Y)
  : isofhlevel n (inserter_type f g).
Proof.
  use isofhleveltotal2.
  - exact HX.
  - intro.
    apply HY.
Defined.

Definition isofhlevel_inserter
           {n : nat}
           {X Y : UU}
           (HX : isofhlevel n X)
           (HY : isofhlevel n Y)
           (f g : X → Y)
  : isofhlevel n (inserter_type f g).
Proof.
  use isofhlevel_inserter_help.
  - exact HX.
  - apply hlevelntosn.
    exact HY.
Defined.

Definition inserter_HLevel
           {n : nat}
           {X Y : HLevel n}
           (f g : pr1 X → pr1 Y)
  : HLevel n.
Proof.
  refine (inserter_type f g ,, _).
  use isofhlevel_inserter.
  - exact (pr2 X).
  - exact (pr2 Y).
Defined.

Definition one_types_inserter_cone
           {X Y : one_types}
           (f g : X --> Y)
  : inserter_cone f g.
Proof.
  use make_inserter_cone.
  - exact (inserter_HLevel f g).
  - exact (inserter_type_pr1 f g).
  - exact (inserter_type_path f g).
Defined.

Definition one_types_inserter_ump_1
           {X Y : one_types}
           (f g : X --> Y)
  : has_inserter_ump_1 (one_types_inserter_cone f g).
Proof.
  intro q.
  use make_inserter_1cell.
  - exact (λ x, inserter_cone_pr1 q x ,, inserter_cone_cell q x).
  - use make_invertible_2cell.
    + exact (λ x, idpath _).
    + apply one_type_2cell_iso.
  - abstract
      (use funextsec ; intro x ; cbn ;
       unfold homotcomp, funhomotsec, homotfun ;
       cbn ;
       rewrite !pathscomp0rid ;
       apply idpath).
Defined.

Definition one_types_inserter_ump_2
           {X Y : one_types}
           (f g : X --> Y)
  : has_inserter_ump_2 (one_types_inserter_cone f g).
Proof.
  intros W u₁ u₂ p r.
  simple refine (_ ,, _).
  - intro x.
    use total2_paths_f.
    + exact (p x).
    + abstract
        (rewrite transportf_paths_FlFr ;
         use path_inv_rotate_ll ;
         pose (eqtohomot r x) as r' ;
         cbn in r' ;
         unfold homotcomp, funhomotsec, homotfun in r' ;
         cbn in r' ;
         rewrite !pathscomp0rid in r' ;
         exact r').
  - abstract
      (use funextsec ;
       intro x ; cbn ;
       unfold homotfun ;
       apply base_total2_paths).
Defined.

Definition one_types_inserter_ump_eq
           {X Y : one_types}
           (f g : X --> Y)
  : has_inserter_ump_eq (one_types_inserter_cone f g).
Proof.
  intros W u₁ u₂ p r φ₁ φ₂ q₁ q₂.
  use funextsec.
  intro x.
  refine (_ @ homotinvweqweq (total2_paths_equiv (λ x, f x = g x) (u₁ x) (u₂ x)) _).
  refine (!(homotinvweqweq (total2_paths_equiv (λ x, f x = g x) (u₁ x) (u₂ x)) _) @ _).
  apply maponpaths.
  use total2_paths_f.
  - exact (eqtohomot q₁ x @ !(eqtohomot q₂ x)).
  - apply (pr2 Y).
Qed.

Definition has_inserters_one_types
  : has_inserters one_types.
Proof.
  intros X Y f g.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (inserter_HLevel f g).
  - exact (inserter_type_pr1 f g).
  - exact (inserter_type_path f g).
  - simple refine (_ ,, _ ,, _).
    + exact (one_types_inserter_ump_1 f g).
    + exact (one_types_inserter_ump_2 f g).
    + exact (one_types_inserter_ump_eq f g).
Defined.

(**
 5. Equifiers
 *)
Definition equifier_type
           {X Y : UU}
           {f g : X → Y}
           (p₁ p₂ : f ~ g)
  : UU
  := ∑ (x : X), p₁ x = p₂ x.

Definition isofhlevel_equifier_help
           {n : nat}
           {X Y : UU}
           (HX : isofhlevel n X)
           (HY : isofhlevel (S(S n)) Y)
           {f g : X → Y}
           (p₁ p₂ : f ~ g)
  : isofhlevel n (equifier_type p₁ p₂).
Proof.
  use isofhleveltotal2.
  - exact HX.
  - intro.
    apply HY.
Defined.

Definition isofhlevel_equifier
           {n : nat}
           {X Y : UU}
           (HX : isofhlevel n X)
           (HY : isofhlevel n Y)
           {f g : X → Y}
           (p₁ p₂ : f ~ g)
  : isofhlevel n (equifier_type p₁ p₂).
Proof.
  use isofhlevel_equifier_help.
  - exact HX.
  - apply hlevelntosn.
    apply hlevelntosn.
    exact HY.
Defined.

Definition equifier_HLevel
           {n : nat}
           {X Y : HLevel n}
           {f g : pr1 X → pr1 Y}
           (p₁ p₂ : f ~ g)
  : HLevel n.
Proof.
  simple refine (_ ,, _).
  - exact (equifier_type p₁ p₂).
  - apply isofhlevel_equifier.
    + exact (pr2 X).
    + exact (pr2 Y).
Defined.

Definition one_types_equifier_pr1
           {X Y : one_types}
           {f g : X --> Y}
           (p₁ p₂ : f ==> g)
  : one_types ⟦ equifier_HLevel p₁ p₂ , X ⟧
  := pr1.

Definition one_types_equifier_eq
           {X Y : one_types}
           {f g : X --> Y}
           (p₁ p₂ : f ==> g)
  : one_types_equifier_pr1 p₁ p₂ ◃ p₁
    =
    one_types_equifier_pr1 p₁ p₂ ◃ p₂.
Proof.
  use funextsec.
  intro x.
  exact (pr2 x).
Qed.

Definition one_types_equifier_cone
           {X Y : one_types}
           {f g : X --> Y}
           (p₁ p₂ : f ==> g)
  : equifier_cone f g p₁ p₂
  := make_equifier_cone
       (equifier_HLevel p₁ p₂ : one_types)
       (one_types_equifier_pr1 p₁ p₂)
       (one_types_equifier_eq p₁ p₂).

Definition one_types_equifier_ump_1
           {X Y : one_types}
           {f g : X --> Y}
           (p₁ p₂ : f ==> g)
  : has_equifier_ump_1 (one_types_equifier_cone p₁ p₂).
Proof.
  intro q.
  use make_equifier_1cell.
  - refine (λ x, equifier_cone_pr1 q x ,, _).
    abstract
      (exact (eqtohomot (equifier_cone_eq q) x)).
  - use make_invertible_2cell.
    + exact (λ x, idpath _).
    + apply one_type_2cell_iso.
Defined.

Definition one_types_equifier_ump_2
           {X Y : one_types}
           {f g : X --> Y}
           (p₁ p₂ : f ==> g)
  : has_equifier_ump_2 (one_types_equifier_cone p₁ p₂).
Proof.
  intros W u₁ u₂ α.
  simple refine (_ ,, _).
  - intro x.
    use total2_paths_f.
    + exact (α x).
    + apply Y.
  - abstract
      (use funextsec ; intro x ; cbn ;
       apply base_total2_paths).
Defined.

Definition one_types_equifier_ump_eq
           {X Y : one_types}
           {f g : X --> Y}
           (p₁ p₂ : f ==> g)
  : has_equifier_ump_eq (one_types_equifier_cone p₁ p₂).
Proof.
  intros W u₁ u₂ α φ₁ φ₂ q₁ q₂.
  use funextsec.
  intro x.
  refine (_ @ homotinvweqweq (total2_paths_equiv (λ x, p₁ x = p₂ x) (u₁ x) (u₂ x)) _).
  refine (!(homotinvweqweq (total2_paths_equiv (λ x, p₁ x = p₂ x) (u₁ x) (u₂ x)) _) @ _).
  apply maponpaths.
  use total2_paths_f.
  - exact (eqtohomot q₁ x @ !(eqtohomot q₂ x)).
  - apply isapropifcontr.
    apply (pr2 Y).
Qed.

Definition has_equifiers_one_types
  : has_equifiers one_types.
Proof.
  intros X Y f g p₁ p₂.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (equifier_HLevel p₁ p₂).
  - exact (one_types_equifier_pr1 p₁ p₂).
  - exact (one_types_equifier_eq p₁ p₂).
  - simple refine (_ ,, _ ,, _).
    + exact (one_types_equifier_ump_1 p₁ p₂).
    + exact (one_types_equifier_ump_2 p₁ p₂).
    + exact (one_types_equifier_ump_eq p₁ p₂).
Defined.
