(* *********************************************************************************** *)
(** * Internal adjunction in displayed bicategories

    Benedikt Ahrens, Marco Maggesi
    April 2018                                                                         *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DispAdjunctions.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Displayed_Local_Univalence.
  Context {C : bicat}.
  Variable (D : disp_prebicat C).

  Definition disp_id2_invertible_2cell
             {a b : C}
             {f : C⟦a, b⟧}
             {aa : D a} {bb : D b}
             (ff : aa -->[ f ] bb)
    : disp_invertible_2cell (id2_invertible_2cell f) ff ff.
  Proof.
    use tpair.
    - exact (disp_id2 ff).
    - use tpair.
      + cbn.
        exact (disp_id2 ff).
      + split ; cbn.
        * exact (disp_id2_left (disp_id2 ff)).
        * exact (disp_id2_left (disp_id2 ff)).
  Defined.

  Definition disp_idtoiso_2_1
             {a b : C}
             {f g : C⟦a, b⟧}
             (p : f = g)
             {aa : D a} {bb : D b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
             (pp : transportf (λ z, _ -->[ z ] _) p ff = gg)
    : disp_invertible_2cell (idtoiso_2_1 f g p) ff gg.
  Proof.
    induction p.
    induction pp.
    exact (disp_id2_invertible_2cell ff).
  Defined.

  Definition disp_locally_univalent
    : UU
    := ∏ (a b : C) (f g : C⟦a,b⟧) (p : f = g) (aa : D a) (bb : D b)
         (ff : aa -->[ f ] bb) (gg : aa -->[ g ] bb),
       isweq (disp_idtoiso_2_1 p ff gg).
End Displayed_Local_Univalence.

Definition transportf_subtypeEquality'
           {A : UU}
           {B : A → UU}
           (Bprop : ∏ (a : A), isaprop (B a))
           {C : A → UU}
           {a : A}
           (b₁ : B a) (b₂ : B a)
           (x : C a)
  : transportf (λ (z : ∑ (x : A), B x), C (pr1 z))
               (@subtypeEquality' A B (a ,, b₁) (a ,, b₂) (idpath _) (Bprop _))
               x
    =
    x.
Proof.
  cbn.
  induction (Bprop a b₁ b₂) as [p q].
  induction p.
  cbn.
  reflexivity.
Defined.

(* TODO: should be moved to Bicat.v or bicategory_laws.v *)
Definition transportf_cell_from_invertible_2cell_eq
           {C : bicat}
           {a b : C}
           {f g : C⟦a,b⟧}
           (Y : f ==> g → UU)
           {α : f ==> g}
           (H₁ : is_invertible_2cell α) (H₂ : is_invertible_2cell α)
           (y : Y α)
  : transportf (λ (z : invertible_2cell f g), Y (pr1 z))
               (@cell_from_invertible_2cell_eq C _ _ _ _
                                               (α ,, H₁) (α ,, H₂)
                                               (idpath α))
               y
    =
    y.
Proof.
  apply transportf_subtypeEquality'.
Qed.

Section Total_Category_Locally_Univalent.
  Context {C : bicat}.
  Variable (D : disp_bicat C)
           (HC : is_univalent_2_1 C)
           (HD : disp_locally_univalent D).
  Local Definition E := (total_bicat D).

  Local Definition path_E
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (f,, ff = g,, gg) ≃ ∑ (p : f = g), transportf _ p ff = gg
    := total2_paths_equiv _ (f ,, ff) (g ,, gg).

  Local Definition path_to_iso_E
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (∑ (p : f = g), transportf _ p ff = gg)
        ≃
        ∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg.
  Proof.
    use weqbandf.
    - exact (idtoiso_2_1 f g ,, HC x y f g).
    - cbn.
      intros p.
      exact (disp_idtoiso_2_1 D p ff gg ,, HD x y f g p xx yy ff gg).
  Defined.

  Definition iso_in_E
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg)
      → (@invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)).
  Proof.
    intros z.
    use tpair.
    - use tpair.
      + exact (pr1 z). (* coerced to a function *)
      + exact (pr2 z).
   - use tpair.
      + use tpair.
        * exact (inv_cell (pr1 z)).
        * exact (disp_inv_cell (pr2 z)).
      + split.
        * cbn.
          use total2_paths_b.
          ** apply vcomp_rinv.
          ** apply disp_vcomp_rinv.
        * cbn.
          use total2_paths_b.
          ** apply vcomp_lid.
          ** apply disp_vcomp_linv.
  Defined.

  Definition iso_in_E_inv
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : @invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)
      → ∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg.
  Proof.
    intros z.
    induction z as [z Hz].
    induction z as [z zz].
    induction Hz as [inv Hz].
    induction inv as [i ii].
    induction Hz as [Hz1 Hz2].
    cbn in *.
    use tpair.
    - exists z.
      use tpair.
      + exact i.
      + cbn.
        split.
        * exact (base_paths _ _ Hz1).
        * exact (base_paths _ _ Hz2).
    - cbn.
      exists zz.
      use tpair.
      + exact ii.
      + cbn.
        split.
        * apply (@transportf_transpose _ (λ α : f ==> f, ff ==>[ α] ff)).
          refine (_ @ fiber_paths Hz1).
          apply (@transportf_paths _ (λ α : f ==> f, ff ==>[ α] ff)).
          apply pathsinv0inv0.
        * apply (@transportf_transpose _ (λ α : g ==> g, gg ==>[ α] gg)).
          refine (_ @ fiber_paths Hz2).
          apply (@transportf_paths _ (λ α : g ==> g, gg ==>[ α] gg)).
          apply pathsinv0inv0.
  Defined.

  Definition iso_in_E_weq
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg)
        ≃
        (@invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)).
  Proof.
    refine (iso_in_E ff gg ,, _).
    use isweq_iso.
    - exact (iso_in_E_inv ff gg).
    - intros z.
      induction z as [z zz].
      use total2_paths2_f.
      + apply cell_from_invertible_2cell_eq.
        reflexivity.
      + use subtypeEquality'.
        * unfold disp_invertible_2cell.
          rewrite pr1_transportf.
          unfold pr1.
          induction zz as [zz Hzz].
          unfold invertible_2cell.
          apply (transportf_cell_from_invertible_2cell_eq (λ z, ff ==>[ z ] gg)).
        * apply isaprop_is_disp_invertible_2cell.
    - intros z.
      destruct z as [z Hz].
      destruct z as [z zz].
      destruct Hz as [inv Hz].
      destruct inv as [i ii].
      destruct Hz as [Hz1 Hz2].
      apply (@cell_from_invertible_2cell_eq E).
      reflexivity.
  Defined.

  Local Definition idtoiso_alt
             {x y : E}
             (f g : E⟦x,y⟧)
    : (idtoiso_2_1 f g
       ~
       (iso_in_E_weq (pr2 f) (pr2 g))
         ∘ (path_to_iso_E (pr2 f) (pr2 g))
         ∘ (path_E (pr2 f) (pr2 g)))%weq.
  Proof.
    intros p.
    induction p.
    apply (@cell_from_invertible_2cell_eq E).
    reflexivity.
  Defined.

  Definition total_is_locally_univalent : is_univalent_2_1 E.
  Proof.
    intros x y f g.
    exact (weqhomot (idtoiso_2_1 f g) _ (invhomot (idtoiso_alt f g))).
  Defined.
End Total_Category_Locally_Univalent.

Definition fiberwise_local_univalent
           {C : bicat}
           (D : disp_bicat C)
  : UU
  := ∏ (a b : C) (f : C ⟦ a, b ⟧) (aa : D a) (bb : D b)
       (ff : aa -->[ f] bb) (gg : aa -->[ f ] bb),
     isweq (disp_idtoiso_2_1 D (idpath f) ff gg).

Definition fiberwise_local_univalent_is_locally_univalent
           {C : bicat}
           (D : disp_bicat C)
           (HD : fiberwise_local_univalent D)
  : disp_locally_univalent D.
Proof.
  intros x y f g p xx yy ff gg.
  induction p.
  apply HD.
Defined.

Section Displayed_Global_Univalence.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Definition disp_idtoiso_2_0
             {a b : C}
             (p : a = b)
             (aa : D a) (bb : D b)
             (pp : transportf (λ z, D z) p aa = bb)
    : disp_internal_adjoint_equivalence (idtoiso_2_0 a b p) aa bb.
  Proof.
    induction p.
    induction pp.
    exact (disp_identity_adjoint_equivalence aa).
  Defined.

  Definition disp_univalent_2_0
    : UU
    := ∏ (a b : C) (p : a = b) (aa : D a) (bb : D b),
       isweq (disp_idtoiso_2_0 p aa bb).
End Displayed_Global_Univalence.

Definition fiberwise_univalent_2_0
           {C : bicat}
           (D : disp_bicat C)
  : UU
  := ∏ (a b : C) (aa bb : D a),
     isweq (disp_idtoiso_2_0 D (idpath a) aa bb).

Definition fiberwise_univalent_2_0_to_disp_univalent_2_0
           {C : bicat}
           (D : disp_bicat C)
  : fiberwise_univalent_2_0 D → disp_univalent_2_0 D.
Proof.
  intros HD.
  intros a b p aa bb.
  induction p.
  exact (HD a a aa bb).
Defined.