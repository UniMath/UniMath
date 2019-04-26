(**
  Monoidal categories

  Based on an implementation by Anthony Bordg.

  Behaviour w.r.t. to swapped tensor product added by Ralph Matthes in 2019
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).
Notation "( c , d )" := (make_precatbinprod c d).
Notation "( f #, g )" := (precatbinprodmor f g).

Section Monoidal_Precat.

Context {C : precategory} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Definition tensor_id {X Y : C} : id X #⊗ id Y = id (X ⊗ Y).
Proof.
  rewrite binprod_id.
  rewrite (functor_id tensor).
  apply idpath.
Defined.

Definition tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') :
  (f · g) #⊗ (f' · g') = f #⊗ f' · g #⊗ g'.
Proof.
  rewrite binprod_comp.
  rewrite (functor_comp tensor).
  apply idpath.
Defined.

Definition is_iso_tensor_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'}
           (f_is_iso : is_iso f) (g_is_iso : is_iso g) : is_iso (f #⊗ g).
Proof.
  exact (functor_on_is_iso_is_iso (is_iso_binprod_iso f_is_iso g_is_iso)).
Defined.

(* I ⊗ - *)
Definition I_pretensor : C ⟶ C := functor_fix_fst_arg _ _ _ tensor I.

Lemma I_pretensor_ok: functor_on_objects I_pretensor = λ c, I ⊗ c.
Proof.
  apply idpath.
Qed.

(* λ *)
Definition left_unitor : UU :=
  nat_iso I_pretensor (functor_identity C).

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C := functor_fix_snd_arg _ _ _ tensor I.

Lemma I_posttensor_ok: functor_on_objects I_posttensor = λ c, c ⊗ I.
Proof.
  apply idpath.
Qed.

(* ρ *)
Definition right_unitor : UU :=
  nat_iso I_posttensor (functor_identity C).

(* (- ⊗ =) ⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite (pair_functor tensor (functor_identity _)) tensor.

Lemma assoc_left_ok: functor_on_objects assoc_left =
  λ c, (ob1 (ob1 c) ⊗ ob2 (ob1 c)) ⊗ ob2 c.
Proof.
  apply idpath.
Qed.

(* - ⊗ (= ⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite
    (precategory_binproduct_unassoc _ _ _)
    (functor_composite (pair_functor (functor_identity _) tensor) tensor).

Lemma assoc_right_ok: functor_on_objects assoc_right =
  λ c, ob1 (ob1 c) ⊗ (ob2 (ob1 c) ⊗ ob2 c).
Proof.
  apply idpath.
Qed.

(* α *)
Definition associator : UU :=
  nat_iso assoc_left assoc_right.
(* This definition goes in the opposite direction of that by Mac Lane (CWM 2nd ed., p.162)
   but conforms to the def. on Wikipedia. *)

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗ id b = pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) =
   pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).

Definition is_strict (eq_λ : I_pretensor = functor_identity C) (λ' : left_unitor)
           (eq_ρ : I_posttensor = functor_identity C) (ρ' : right_unitor)
           (eq_α : assoc_left = assoc_right) (α' : associator) : UU :=
  (is_nat_iso_id eq_λ λ') × (is_nat_iso_id eq_ρ ρ') × (is_nat_iso_id eq_α α').

End Monoidal_Precat.

Definition monoidal_precat : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
         (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').


Definition monoidal_precat_struct : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor, unit.

Definition mk_monoidal_precat_struct (C: precategory)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor): monoidal_precat_struct :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, tt)))))).

Definition mk_monoidal_precat (C: precategory)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor)
  (eq1: triangle_eq tensor I λ' ρ' α')(eq2: pentagon_eq tensor α'): monoidal_precat :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, (eq1,, eq2))))))).

Section Monoidal_Precat_Accessors.

Context (M : monoidal_precat).

Definition monoidal_precat_precat := pr1 M.

Definition monoidal_precat_tensor := pr1 (pr2 M).

Definition monoidal_precat_unit := pr1 (pr2 (pr2 M)).

Definition monoidal_precat_left_unitor := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_precat_right_unitor := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_precat_associator := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition monoidal_precat_eq := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

End Monoidal_Precat_Accessors.

Definition strict_monoidal_precat : UU :=
  ∑ M : monoidal_precat,
  ∏ (eq_λ : I_pretensor (monoidal_precat_tensor M) (monoidal_precat_unit M) =
  functor_identity (pr1 M)),
  ∏ (eq_ρ : I_posttensor (monoidal_precat_tensor M) (monoidal_precat_unit M) =
  functor_identity (pr1 M)),
  ∏ (eq_α : assoc_left (monoidal_precat_tensor M) =
  assoc_right (monoidal_precat_tensor M)),
  is_strict (monoidal_precat_tensor M) (monoidal_precat_unit M) eq_λ (monoidal_precat_left_unitor M) eq_ρ (monoidal_precat_right_unitor M) eq_α (monoidal_precat_associator M).

Section swapped_tensor.

  Context (M : monoidal_precat).

  Let C := monoidal_precat_precat M.
  Let tensor := monoidal_precat_tensor M.

Definition swapping_of_tensor: C ⊠ C ⟶ C := functor_composite binswap_pair_functor tensor.

Definition associator_swapping_of_tensor: associator swapping_of_tensor.
Proof.
  set (α := monoidal_precat_associator M).
  set (α' := nat_iso_to_trans_inv α).
  red.
  set (trafo := (pre_whisker reverse_three_args α'): (assoc_left swapping_of_tensor) ⟹ (assoc_right swapping_of_tensor)).
  assert (tisiso: is_nat_iso trafo).
  { red. intro c. set (aux := pr2 (nat_iso_inv α)).
    apply (pre_whisker_iso_is_iso reverse_three_args α' aux).
  }
  exact (trafo,, tisiso).
Defined.

Lemma triangle_eq_swapping_of_tensor: triangle_eq swapping_of_tensor (monoidal_precat_unit M)
  (monoidal_precat_right_unitor M) (monoidal_precat_left_unitor M) associator_swapping_of_tensor.
Proof.
  red. intros a b. cbn.
  set (H := pr1 (monoidal_precat_eq M)).
  unfold triangle_eq in H.
  eapply pathscomp0.
  2: { apply cancel_precomposition.
       apply pathsinv0.
       apply H. }
  clear H.
  rewrite assoc.
  eapply pathscomp0.
  { apply pathsinv0.
    apply id_left. }
  apply cancel_postcomposition.
  apply pathsinv0.
  apply iso_after_iso_inv.
Qed.

Lemma pentagon_eq_swapping_of_tensor: pentagon_eq swapping_of_tensor associator_swapping_of_tensor.
Proof.
  red. intros a b c d. cbn.
  set (H := pr2 (monoidal_precat_eq M)).
  unfold pentagon_eq in H.
  apply iso_inv_on_right.
  apply pathsinv0.
  apply inv_iso_unique'.
  unfold precomp_with.
  rewrite assoc.
  eapply pathscomp0.
  { apply cancel_postcomposition.
    apply H. }
  clear H.
  repeat rewrite assoc.
  eapply pathscomp0.
  { do 2 apply cancel_postcomposition.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    apply (functor_comp (functor_fix_fst_arg _ _ _ tensor d)).
  }
  eapply pathscomp0.
  { do 2 apply cancel_postcomposition.
    apply cancel_precomposition.
    apply maponpaths.
    apply (iso_inv_after_iso (mk_iso (pr2 (monoidal_precat_associator M) ((c, b), a)))). }
  rewrite functor_id.
  rewrite id_right.
  eapply pathscomp0.
  { apply cancel_postcomposition.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply (iso_inv_after_iso (mk_iso (pr2 (monoidal_precat_associator M) ((d, tensor (c, b)), a)))). }
  rewrite id_right.
  eapply pathscomp0.
  apply pathsinv0.
  apply (functor_comp (functor_fix_snd_arg _ _ _ tensor a)).
  eapply pathscomp0.
  { apply maponpaths.
    apply (iso_inv_after_iso (mk_iso (pr2 (monoidal_precat_associator M) ((d, c), b)))). }
  use functor_id.
Qed.

Definition swapping_of_monoidal_precat: monoidal_precat.
Proof.
  use (mk_monoidal_precat C swapping_of_tensor).
  - exact (monoidal_precat_unit M).
  - apply monoidal_precat_right_unitor.
  - apply monoidal_precat_left_unitor.
  - exact associator_swapping_of_tensor.
  - exact triangle_eq_swapping_of_tensor.
  - exact pentagon_eq_swapping_of_tensor.
Defined.

End swapped_tensor.
