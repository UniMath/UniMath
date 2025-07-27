(*******************************************************************************************

 Category of paired functors between posetal fibrations

 As part of "Weakest Precondition in Fibrations" (https://doi.org/10.1016/j.entcs.2020.09.002),
 the notion of fibered functors allows us to depict effects and their liftings to a predicate category
 as objects in the category Pos-Fib.

 Contents:
  1. Lax slice displayed category
  2. Pos-Fib for the domain fibation

 TODO: Implement a more general version (2-category, where 0-cells are posetal fibrations).
 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.MoreFoundations.All.

Local Open Scope cat.

Section PosFib.
Context (C : category)
        (Ω : C)
        (leq : ∏ X : ob C, C⟦X, Ω⟧ → C⟦X, Ω⟧ → hProp)
        (is_po_leq : ∏ X : ob C, isPartialOrder (leq X))
        (is_precomp_monotone_leq :  ∏ (X Y : ob C) (f : C⟦X, Y⟧)
        (g h : C⟦Y, Ω⟧),
        leq Y g h → leq X (g ∘ f) (h ∘ f)).

Definition lax_slice_ob_mor : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - exact (λ X, C⟦X,Ω⟧).
  - exact (λ X Y i j h, leq X i (h · j)).
Defined.


Definition lax_slice_id_comp : disp_cat_id_comp C lax_slice_ob_mor.
Proof.
  split.
  - intros. simpl. rewrite id_left. apply is_po_leq.
  - simpl. intros. destruct (is_po_leq x) as [[trans _] _]. apply trans with (x2 := f · yy).
    + apply X.
    + rewrite assoc'. apply is_precomp_monotone_leq. apply X0.
Defined. 

Definition lax_slice_data : disp_cat_data C := 
  (lax_slice_ob_mor,, lax_slice_id_comp).

Definition lax_slice_axioms : disp_cat_axioms C lax_slice_data.
Proof.
  repeat apply tpair; intros;
  try (apply proofirrelevance, pr2).
  apply isasetaprop, pr2.
Qed.

Definition lax_slice_disp : disp_cat C := 
  (lax_slice_data,, lax_slice_axioms).

Definition lax_slice_cleaving : cleaving lax_slice_disp.
Proof.
  intros c' c f g. use tpair.
  - exact (f · g).
  - use tpair.
    + apply (is_po_leq c).
    + intros x f' h is_leq_h.
      use iscontraprop1. 
      * apply iscontraprop1.
        ** apply isapropisaprop. 
        ** apply isofhleveltotal2.
          *** exact (pr2 (leq _ h (f' · (f · g)))).
          *** intros is_leq_h' path path'.
              apply (isofhlevelcontr 2).
              exists is_leq_h.
              intros is_leq_h''.
              apply proofirrelevance.
              apply pr2.
      * exists (transportf (λ z, leq _ h z) (assoc'  f' f g) is_leq_h).
        apply proofirrelevance, pr2.
Defined.

Let proj_funct : functor (total_category lax_slice_disp) C := pr1_category lax_slice_disp.

Definition disp_fibered_functor_cat : disp_cat (functor_category C C).
Proof.
  use disp_struct.
  - simpl. intro F. 
    exact (∑ F' : disp_functor F lax_slice_disp lax_slice_disp,
    preserves_cleaving lax_slice_cleaving lax_slice_cleaving F').
  - simpl. intros F G [F' is_fibered_F'] [G' is_fibered_G'] α.
    exact (disp_nat_trans α F' G').
  - simpl. intros F G [F' is_fibered_F'] [G' is_fibered_G'] α.
    unfold isaprop.
    unfold isofhlevel. 
    intros α' α''.
    apply isapropifcontr.
    apply iscontraprop1.
    apply  isofhleveltotal2.
    + do 2 (apply impred; intro).
      apply isapropifcontr.
      apply iscontraprop1.
      * apply pr2.
      * apply  α'.
    + intros x x' x''.
      apply isapropifcontr.
      apply iscontraprop1.
      set (D' := disp_functor_data_from_disp_functor F').
      set (D'' := disp_functor_data_from_disp_functor G').
      change (disp_nat_trans_data α D' D'') in x.
      apply (isaprop_disp_nat_trans_axioms α x).
      exact x'.
    + exact α'.
  - intros F [F' is_fibered_F'].
    apply (disp_nat_trans_id  F').
  - intros F G H [F' is_fibered_F'] [G' is_fibered_G'] [H' is_fibered_H'] α β α' β'. 
    exact (@disp_nat_trans_comp _ _ _ _ _ _ _ lax_slice_disp lax_slice_disp _ _ _ α' β').
Defined.

Definition pos_fib_cat : category := total_category disp_fibered_functor_cat.

End PosFib.