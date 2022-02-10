(*********************************************************************************

 Colimits of 1-types

 Contents:
 1. Initial object
 2. Coproducts
 3. Extensivity

 *********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.Limits.Examples.OneTypesLimits.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.
Require Import UniMath.Bicategories.Colimits.Extensive.

Local Open Scope cat.

(**
 1. Initial object
 *)

(** MOVE ??? *)
Definition empty_hlevel
           (n : nat)
  : isofhlevel (n + 1) ∅.
Proof.
  induction n.
  - exact isapropempty.
  - exact (λ x, fromempty x).
Defined.

Definition empty_one_type
  : one_types
  := (∅ ,, empty_hlevel 2).

Definition empty_is_biinitial_one_types
  : is_biinitial empty_one_type.
Proof.
  use make_is_biinitial.
  - exact (λ _, fromempty).
  - exact (λ _ _ _ z, fromempty z).
  - exact (λ _ _ _ _ _, funextsec _ _ _ (λ z, fromempty z)).
Defined.

Definition biinitial_obj_one_types
  : biinitial_obj one_types
  := empty_one_type ,, empty_is_biinitial_one_types.

Definition strict_biinitial_one_types
  : is_strict_biinitial_obj empty_one_type.
Proof.
  refine (empty_is_biinitial_one_types ,, _).
  intros X f.
  use weq_is_adjoint_equivalence.
  apply isweqtoempty.
Defined.

(**
 2. Coproducts
 *)
Definition coprod_one_types
           (X Y : one_type)
  : one_type.
Proof.
  use make_one_type.
  - exact (X ⨿ Y).
  - apply isofhlevelssncoprod.
    + apply X.
    + apply Y.
Defined.

Definition bincoprod_cocone_one_types
           (X Y : one_types)
  : bincoprod_cocone X Y.
Proof.
  use make_bincoprod_cocone.
  - exact (coprod_one_types X Y).
  - exact inl.
  - exact inr.
Defined.

Section CoprodUMP.
  Context (X Y : one_types).

  Definition binprod_cocone_has_binprod_ump_1_one_types
    : bincoprod_ump_1 (bincoprod_cocone_one_types X Y).
  Proof.
    intros Z.
    use make_bincoprod_1cell.
    - cbn ; intro z.
      induction z as [ x | y ].
      + exact (bincoprod_cocone_inl Z x).
      + exact (bincoprod_cocone_inr Z y).
    - use make_invertible_2cell.
      + intro ; apply idpath.
      + apply one_type_2cell_iso.
    - use make_invertible_2cell.
      + intro ; apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition binprod_cocone_has_binprod_ump_2_one_types
    : bincoprod_ump_2 (bincoprod_cocone_one_types X Y).
  Proof.
    intros Z φ ψ α β.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros γ₁ γ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use funextsec ; intro z ;
         induction z as [ x | y ] ;
         [ exact (eqtohomot (pr12 γ₁) x @ !(eqtohomot (pr12 γ₂) x))
         | exact (eqtohomot (pr22 γ₁) y @ !(eqtohomot (pr22 γ₂) y)) ]).
    - simple refine (_ ,, _ ,, _).
      + cbn ; intro z.
        induction z as [ x | y ].
        * exact (α x).
        * exact (β y).
      + abstract
          (use funextsec ;
           intro z ; cbn ;
           apply idpath).
      + abstract
          (use funextsec ;
           intro z ; cbn ;
           apply idpath).
  Defined.

  Definition binprod_cocone_has_binprod_ump_one_types
    : has_bincoprod_ump (bincoprod_cocone_one_types X Y).
  Proof.
    split.
    - exact binprod_cocone_has_binprod_ump_1_one_types.
    - exact binprod_cocone_has_binprod_ump_2_one_types.
  Defined.
End CoprodUMP.

Definition has_bincoprod_one_types
  : has_bincoprod one_types
  := λ X Y,
     bincoprod_cocone_one_types X Y
     ,,
     binprod_cocone_has_binprod_ump_one_types X Y.

Definition one_types_with_biinitial_bincoprod
  : bicat_with_biinitial_bincoprod
  := one_types ,, biinitial_obj_one_types ,, has_bincoprod_one_types.

(**
 3. Extensivity
 *)
Section OneTypesDisjoint.
  Notation "∁" := one_types_with_biinitial_bincoprod.

  Context (X Y : ∁).

  Let ι₁ : X --> pr1 (bincoprod_of ∁ X Y)
    := bincoprod_cocone_inl (pr1 (bincoprod_of ∁ X Y)).
  Let ι₂ : Y --> pr1 (bincoprod_of ∁ X Y)
    := bincoprod_cocone_inr (pr1 (bincoprod_of ∁ X Y)).

  Definition one_types_inl_inr
    : has_comma_ump (@biinitial_comma_cone ∁ _ _ _ ι₁ ι₂).
  Proof.
    split.
    - intro Z.
      use make_comma_1cell.
      + intro z.
        exact (fromempty (negpathsii1ii2 _ _ (comma_cone_cell Z z))).
      + use make_invertible_2cell.
        * intro z.
          exact (fromempty (negpathsii1ii2 _ _ (comma_cone_cell Z z))).
        * apply one_type_2cell_iso.
      + use make_invertible_2cell.
        * intro z.
          exact (fromempty (negpathsii1ii2 _ _ (comma_cone_cell Z z))).
        * apply one_type_2cell_iso.
      + abstract
          (use funextsec ;
           intro z ;
           exact (fromempty (negpathsii1ii2 _ _ (comma_cone_cell Z z)))).
    - intros Z φ ψ α β p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros τ₁ τ₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           use funextsec ;
           intro z ;
           exact (fromempty (φ z))).
      + simple refine (_ ,, _ ,, _).
        * intro z.
          exact (fromempty (φ z)).
        * abstract
            (use funextsec ;
             intro z ;
             exact (fromempty (φ z))).
        * abstract
            (use funextsec ;
             intro z ;
             exact (fromempty (φ z))).
  Defined.

  Definition one_types_inr_inl
    : has_comma_ump (@biinitial_comma_cone ∁ _ _ _ ι₂ ι₁).
  Proof.
    split.
    - intro Z.
      use make_comma_1cell.
      + intro z.
        exact (fromempty (negpathsii2ii1 _ _ (comma_cone_cell Z z))).
      + use make_invertible_2cell.
        * intro z.
          exact (fromempty (negpathsii2ii1 _ _ (comma_cone_cell Z z))).
        * apply one_type_2cell_iso.
      + use make_invertible_2cell.
        * intro z.
          exact (fromempty (negpathsii2ii1 _ _ (comma_cone_cell Z z))).
        * apply one_type_2cell_iso.
      + abstract
          (use funextsec ;
           intro z ;
           exact (fromempty (negpathsii2ii1 _ _ (comma_cone_cell Z z)))).
    - intros Z φ ψ α β p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros τ₁ τ₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           use funextsec ;
           intro z ;
           exact (fromempty (φ z))).
      + simple refine (_ ,, _ ,, _).
        * intro z.
          exact (fromempty (φ z)).
        * abstract
            (use funextsec ;
             intro z ;
             exact (fromempty (φ z))).
        * abstract
            (use funextsec ;
             intro z ;
             exact (fromempty (φ z))).
  Defined.
End OneTypesDisjoint.

Section OneTypesUniversal.
  Notation "∁" := one_types_with_biinitial_bincoprod.

  Context {X Y Z : ∁}
          (h : Z --> pr1 (bincoprod_of ∁ X Y)).

  Let ι₁ : one_types ⟦ X , pr1 (bincoprod_of ∁ X Y) ⟧
    := inl.
  Let ι₂ : one_types ⟦ Y , pr1 (bincoprod_of ∁ X Y) ⟧
      := inr.

  Let κ₁ : one_types ⟦ hfp_HLevel 3 _ h , Z ⟧
    := hfpg' ι₁ h.
  Let κ₂ : one_types ⟦ hfp_HLevel 3 _ h , Z ⟧
    := hfpg' ι₂ h.

  Definition one_types_universal_coprod_map
             (W : @bincoprod_cocone
                    ∁
                    (hfp_HLevel 3 ι₁ h)
                    (hfp_HLevel 3 ι₂ h))
    : ∏ (z : pr1 Z)
        (q : pr1 X ⨿ pr1 Y)
        (p : h z = q),
      pr11 W.
  Proof.
    intros z q.
    induction q as [ x | y ].
    - intro p.
      refine (bincoprod_cocone_inl W _).
      exact ((x ,, z) ,, p).
    - intro p.
      refine (bincoprod_cocone_inr W _).
      exact ((y ,, z) ,, p).
  Defined.

  Definition one_types_universal_coprod_map_idpath
             (W : @bincoprod_cocone
                    ∁
                    (hfp_HLevel
                       3
                       (bincoprod_cocone_inl (pr1 (bincoprod_of ∁ X Y)))
                       h)
                    (hfp_HLevel
                       3
                       (bincoprod_cocone_inr (pr1 (bincoprod_of ∁ X Y)))
                       h))
             (z : pr1 Z)
             (q : pr1 X ⨿ pr1 Y)
             (p : h z = q)
    : one_types_universal_coprod_map W z q p
      =
      one_types_universal_coprod_map W z (h z) (idpath _).
  Proof.
    induction p.
    apply idpath.
  Defined.

  Section Universal.
    Context {W : one_types}
            {φ ψ : Z --> W}
            (α : κ₁ · φ ==> κ₁ · ψ)
            (β : κ₂ · φ ==> κ₂ · ψ).

    Definition one_types_universal_coprod_cell_help
               (z : pr1 Z)
               (q : pr111 (bincoprod_of ∁ X Y))
               (p : h z = q)
      : φ z = ψ z.
    Proof.
      cbn in z, p, q.
      induction q as [ x | y ].
      - exact (α ((x ,, z) ,, p)).
      - exact (β ((y ,, z) ,, p)).
    Defined.

    Definition one_types_universal_coprod_cell_help_eq
               (z : pr1 Z)
               (q : pr111 (bincoprod_of ∁ X Y))
               (p : h z = q)
      : one_types_universal_coprod_cell_help z (h z) (idpath _)
        =
        one_types_universal_coprod_cell_help z q p.
    Proof.
      induction p.
      apply idpath.
    Qed.

    Definition one_types_universal_coprod_cell
      : φ ==> ψ
      := λ z, one_types_universal_coprod_cell_help z (h z) (idpath _).

    Definition one_types_universal_coprod_cell_inl
      : funhomotsec (hfpg' inl h) one_types_universal_coprod_cell = α.
    Proof.
      use funextsec.
      intro z.
      unfold funhomotsec, one_types_universal_coprod_cell.
      exact (one_types_universal_coprod_cell_help_eq _ _ (pr2 z)).
    Qed.

    Definition one_types_universal_coprod_cell_inr
      : funhomotsec (hfpg' inr h) one_types_universal_coprod_cell = β.
    Proof.
      use funextsec.
      intro z.
      unfold funhomotsec, one_types_universal_coprod_cell.
      exact (one_types_universal_coprod_cell_help_eq _ _ (pr2 z)).
    Qed.

    Definition one_types_universal_coprod_unique
      : isaprop
          (∑ (γ : φ ==> ψ),
           bincoprod_cocone_inl (make_bincoprod_cocone Z κ₁ κ₂) ◃ γ = α
           ×
           bincoprod_cocone_inr (make_bincoprod_cocone Z κ₁ κ₂) ◃ γ = β).
    Proof.
      use invproofirrelevance.
      intros τ₁ τ₂.
      use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
      use funextsec.
      intro z.
      pose (q := h z).
      assert (p : h z = q).
      {
        apply idpath.
      }
      induction q as [ x | y ].
      - exact (eqtohomot (pr12 τ₁) ((x ,, z) ,, p)
               @ !(eqtohomot (pr12 τ₂) ((x ,, z) ,, p))).
      - exact (eqtohomot (pr22 τ₁) ((y ,, z) ,, p)
               @ !(eqtohomot (pr22 τ₂) ((y ,, z) ,, p))).
    Qed.
  End Universal.

  Definition one_types_universal_coprod
    : has_bincoprod_ump
        (@make_bincoprod_cocone
           ∁
           (hfp_HLevel 3 _ h)
           (hfp_HLevel 3 _ h)
           Z
           (hfpg' inl h)
           (hfpg' inr h)).
  Proof.
    split.
    - intro W.
      use make_bincoprod_1cell.
      + intro z ; cbn.
        exact (one_types_universal_coprod_map W z (h z) (idpath _)).
      + use make_invertible_2cell.
        * intro z.
          induction z as [ [ x z ] p ] ; cbn in *.
          exact (!one_types_universal_coprod_map_idpath W z (inl x) p).
        * apply one_type_2cell_iso.
      + use make_invertible_2cell.
        * intro z.
          induction z as [ [ x z ] p ] ; cbn in *.
          exact (!one_types_universal_coprod_map_idpath W z (inr x) p).
        * apply one_type_2cell_iso.
    - intros W φ ψ α β.
      use iscontraprop1.
      + apply one_types_universal_coprod_unique.
      + simple refine (_ ,, _ ,, _).
        * exact (one_types_universal_coprod_cell α β).
        * exact (one_types_universal_coprod_cell_inl α β).
        * exact (one_types_universal_coprod_cell_inr α β).
  Defined.
End OneTypesUniversal.

Definition is_extensive_one_types
  : is_extensive one_types_with_biinitial_bincoprod.
Proof.
  intros X Y.
  split.
  - refine (_ ,, _ ,, _ ,, _).
    + apply one_types_isInjective_fully_faithful_1cell ; cbn.
      apply isweqonpathsincl.
      apply isinclii1.
    + apply one_types_isInjective_fully_faithful_1cell ; cbn.
      apply isweqonpathsincl.
      apply isinclii2.
    + exact (one_types_inl_inr X Y).
    + exact (one_types_inr_inl X Y).
  - use is_universal_from_pb_alt.
    + exact one_types_has_pb.
    + intros Z h.
      exact (one_types_universal_coprod h).
Defined.
