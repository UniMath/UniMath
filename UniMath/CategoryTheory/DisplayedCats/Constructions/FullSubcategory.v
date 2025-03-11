(**************************************************************************************************

  The displayed construction of a full subcategory

  If we construct a displayed category where the structure on the morphisms is the unit type, and
  the structure on the objects is a proposition, then the resulting total category is a full
  subcategory of the base category.
  Because both the morphisms and the equalities of the objects in the resulting subcategory are
  inherited from the base category, the resulting category is univalent if the base category is.
  If we send the data `p : P c` to its truncation `hinhpr p : ∥ P c ∥`, we get a displayed functor
  over the identity, and this truncation functor is a weak equivalence.

  Contents
  1. The construction of the full subcategory as a displayed category [disp_full_sub]
  2. Univalence [disp_full_sub_univalent]
  3. Shortcuts for just the resulting total category [full_subcat] [is_univalent_full_subcat]
  4. The truncation functor [truncation_functor]

 **************************************************************************************************)
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

(** * 1. The construction of the full subcategory as a displayed category *)

Definition disp_full_sub_ob_mor (C : precategory_ob_mor) (P : C → UU)
  : disp_cat_ob_mor C
  := (P,, (λ a b aa bb f, unit)).

Definition disp_full_sub_id_comp (C : precategory_data) (P : C → UU)
  : disp_cat_id_comp C (disp_full_sub_ob_mor C P).
Proof.
  split; intros; apply tt.
Defined.

Definition disp_full_sub_data (C : precategory_data) (P : C → UU)
  : disp_cat_data C
  :=  disp_full_sub_ob_mor C P,, disp_full_sub_id_comp C P.

Lemma disp_full_sub_locally_prop (C : category) (P : C → UU) :
  locally_propositional (disp_full_sub_data C P).
Proof.
  intro; intros; apply isapropunit.
Qed.

Definition disp_full_sub (C : category) (P : C → UU)
  : disp_cat C.
Proof.
  use make_disp_cat_locally_prop.
  - exact (disp_full_sub_data C P).
  - apply disp_full_sub_locally_prop.
Defined.

(** * 2. Univalence *)

Lemma disp_full_sub_univalent (C : category) (P : C → UU) :
  (∏ x : C, isaprop (P x)) →
  is_univalent_disp (disp_full_sub C P).
Proof.
  intro HP.
  apply is_univalent_disp_from_fibers.
  intros x xx xx'. cbn in *.
  apply isweqcontrprop. apply HP.
  apply isofhleveltotal2.
  - apply isapropunit.
  - intro. apply (@isaprop_is_z_iso_disp _ (disp_full_sub C P)).
Defined.

(** * 3. Shortcuts for just the resulting total category *)

Definition full_subcat (C : category) (P : C → UU) : category := total_category (disp_full_sub C P).

Definition full_subcat_pr1_fully_faithful
  (C : category)
  (P : C → UU)
  : fully_faithful (pr1_category (disp_full_sub C P))
  := fully_faithful_pr1_category _ (λ (a b : full_subcat _ _) _, iscontrunit).

Definition is_univalent_full_subcat (C : category) (univC : is_univalent C) (P : C → UU) :
  (∏ x : C, isaprop (P x)) → is_univalent (full_subcat C P).
Proof.
  intro H.
  apply is_univalent_total_category.
  - exact univC.
  - exact (disp_full_sub_univalent _ _ H).
Defined.

(** * 4. The truncation functor *)
Section TruncationFunctor.

  Context {C : category}.
  Context (P : C → UU).

  Definition disp_truncation_functor
    : disp_functor
      (functor_identity C)
      (disp_full_sub C P)
      (disp_full_sub C (λ X, ∥ P X ∥)).
  Proof.
    use tpair.
    - use tpair.
      + exact (λ X, hinhpr).
      + exact (λ X Y HX HY f, idfun unit).
    - abstract easy.
  Defined.

  Definition truncation_functor
    : full_subcat C P ⟶ full_subcat C (λ X, ∥ P X ∥)
    := total_functor disp_truncation_functor.

  Lemma truncation_functor_fully_faithful
    : fully_faithful truncation_functor.
  Proof.
    intros X Y.
    apply idisweq.
  Defined.

  Lemma truncation_functor_essentially_surjective
    : essentially_surjective truncation_functor.
  Proof.
    intro X.
    refine (hinhfun _ (pr2 X)).
    intro HX.
    exists (pr1 X ,, HX).
    apply (weq_ff_functor_on_z_iso (full_subcat_pr1_fully_faithful _ _)).
    apply identity_z_iso.
  Defined.

End TruncationFunctor.
