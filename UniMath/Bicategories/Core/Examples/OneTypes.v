(**
The bicategory of 1-types.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
*)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Definition one_type
  : UU
  := HLevel 3.

Definition make_one_type
           (X : UU)
           (i : isofhlevel 3 X)
  : one_type
  := tpair (λ A, isofhlevel 3 A) X i.

Definition one_type_to_type : one_type -> UU := pr1.
Coercion one_type_to_type : one_type >-> UU.

Definition one_type_isofhlevel
           (X : one_type)
  : isofhlevel 3 X.
Proof.
  apply X.
Defined.

(** The bicategory *)
Definition one_type_bicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact one_type.
  - exact (λ X Y, X → Y).
  - exact (λ _ _ f g, f ~ g).
  - exact (λ _ x, x).
  - exact (λ _ _ _ f g x, g(f x)).
  - intros. exact (homotrefl _).
  - cbn ; intros X Y f g h p q.
    exact (homotcomp p q).
  - cbn ; intros X Y Z f g h p. exact (funhomotsec f p).
  - cbn ; intros X Y Z f g h p. exact (homotfun p h).
  - intros. intro. reflexivity.
  - intros. intro. reflexivity.
  - intros. intro. reflexivity.
  - intros. intro. reflexivity.
  - intros. intro. reflexivity.
  - intros. intro. reflexivity.
Defined.

Definition one_type_bicat_laws
  : prebicat_laws one_type_bicat_data.
Proof.
  repeat (use tpair).
  - intros X Y f g p ; cbn in *.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    unfold homotcomp, homotrefl.
    apply funextsec. intro x.
    apply pathscomp0rid.
  - intros X Y f g h k p q r.
    apply funextsec. intro x.
    apply path_assoc.
  - reflexivity.
  - reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    apply funextsec. intro x.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    apply funextsec. intro x.
    unfold homotcomp, homotfun. simpl.
    apply (! maponpathscomp0 _ _ _).
  - intros X Y f g p ; cbn in *.
    apply funextsec. intro x.
    unfold homotcomp, homotfun. simpl.
    apply pathscomp0rid.
  - intros X Y f g p ; cbn in *.
    apply funextsec. intro x.
    unfold homotcomp, homotfun. simpl.
    etrans. apply pathscomp0rid.
    apply maponpathsidfun.
  - intros W X Y Z f g h i p ; cbn in *.
    apply funextsec. intro x.
    unfold homotcomp, funhomotsec. simpl.
    apply pathscomp0rid.
  - intros W X Y Z f g h i p ; cbn in *.
    apply funextsec. intro x.
    apply pathscomp0rid.
  - intros W X Y Z f g h i p ; cbn in *.
    apply funextsec. intro x.
    unfold homotcomp, homotfun. simpl.
    etrans. apply maponpathscomp.
    apply (! pathscomp0rid _).
  - intros X Y Z f g h i p q ; cbn in *.
    apply funextsec. intro x.
    unfold homotcomp, homotfun, funhomotsec.
    induction (p x). apply (! pathscomp0rid _).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros V W X Y Z f g h i ; cbn in *.
    reflexivity.
Qed.

Definition one_types
  : bicat.
Proof.
  use build_bicategory.
  - exact one_type_bicat_data.
  - exact one_type_bicat_laws.
  - intros X Y f g ; cbn in *.
    apply (impred 2 (λ x, f x = g x)).
    exact (λ x, pr2 Y (f x) (g x)).
Defined.

(** Each 2-cell is an iso *)
Definition one_type_2cell_iso
           {X Y : one_types}
           {f g : one_types⟦X,Y⟧}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  refine (invhomot α ,, _).
  split ; cbn.
  - apply funextsec. intro x. apply pathsinv0r.
  - apply funextsec. intro x. apply pathsinv0l.
Defined.

(** It is univalent *)
Definition one_types_is_univalent_2_1
  : is_univalent_2_1 one_types.
Proof.
  intros X Y f g.
  use isweq_iso.
  - intros α. apply funextsec. apply α.
  - intros p.
    induction p ; cbn.
    change (homotrefl f) with (toforallpaths _ f f (idpath f)).
    apply funextsec_toforallpaths.
  - intros α. cbn.
    use subtypePath ; cbn.
    + intro. exact (@isaprop_is_invertible_2cell one_types X Y f g _).
    + etrans. 2:{ apply toforallpaths_funextsec. }
      unfold idtoiso_2_1, toforallpaths. cbn.
      apply funextsec. intro x.
      induction (funextsec _ f g (pr1 α)).
      reflexivity.
Defined.

Definition adjoint_equivalence_is_weq
           {X Y : one_types}
           (f : one_types⟦X,Y⟧)
           (Hf : left_adjoint_equivalence f)
  : isweq f.
Proof.
  use isweq_iso.
  - exact (left_adjoint_right_adjoint Hf).
  - intros x.
    exact (!left_adjoint_unit Hf x).
  - intros x.
    exact (left_adjoint_counit Hf x).
Defined.

Definition weq_is_adjoint_equivalence_help
           {X Y : one_types}
           (f : one_types⟦X,Y⟧)
           (Hf : isweq f)
  : left_equivalence f.
Proof.
  use tpair.
  - refine (invmap (f ,, Hf) ,, _).
    split.
    + intros x.
      exact (!(homotinvweqweq (f ,, Hf) x)).
    + intros x.
      exact (homotweqinvweq (f ,, Hf) x).
  - split ; apply one_type_2cell_iso.
Defined.

Definition adjequiv_to_weq (X Y : one_types)
  : (pr1 X ≃ pr1 Y) ≃ adjoint_equivalence X Y.
Proof.
  use weqfibtototal.
  intro f.
  apply weqimplimpl.
  - intro Hf.
    apply equiv_to_isadjequiv.
    exact (weq_is_adjoint_equivalence_help f Hf).
  - exact (adjoint_equivalence_is_weq f).
  - apply isapropisweq.
  - apply isaprop_left_adjoint_equivalence.
    exact one_types_is_univalent_2_1.
Defined.

Definition idoiso_2_0_onetypes (X Y : one_types)
  : X = Y ≃ adjoint_equivalence X Y
  := (adjequiv_to_weq X Y ∘ UA_for_HLevels 3 X Y)%weq.

Definition one_types_is_univalent_2_0
  : is_univalent_2_0 one_types.
Proof.
  intros X Y.
  use weqhomot.
  - exact (idoiso_2_0_onetypes X Y).
  - intros p.
    induction p ; cbn.
    apply path_internal_adjoint_equivalence.
    + apply one_types_is_univalent_2_1.
    + reflexivity.
Defined.

Definition one_types_is_univalent_2
  : is_univalent_2 one_types.
Proof.
  split.
  - exact one_types_is_univalent_2_0.
  - exact one_types_is_univalent_2_1.
Defined.
