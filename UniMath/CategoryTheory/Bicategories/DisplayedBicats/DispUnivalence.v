(* *********************************************************************************** *)
(** * Internal adjunction in displayed bicategories

    Benedikt Ahrens, Marco Maggesi
    April 2018                                                                         *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
(* For showing that the being a displayed adjoint equivalence is a proposition *)
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Export UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Export UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Export UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Displayed_Local_Univalence.
  Context {C : bicat}.
  Variable (D : disp_prebicat C).

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

  Definition disp_univalent_2_1
    : UU
    := ∏ (a b : C) (f g : C⟦a,b⟧) (p : f = g) (aa : D a) (bb : D b)
         (ff : aa -->[ f ] bb) (gg : aa -->[ g ] bb),
       isweq (disp_idtoiso_2_1 p ff gg).
End Displayed_Local_Univalence.


Section Total_Category_Univalent_2_1.
  Context {C : bicat}.
  Variable (D : disp_bicat C)
           (HC : is_univalent_2_1 C)
           (HD : disp_univalent_2_1 D).
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

  Definition total_is_univalent_2_1 : is_univalent_2_1 E.
  Proof.
    intros x y f g.
    exact (weqhomot (idtoiso_2_1 f g) _ (invhomot (idtoiso_alt f g))).
  Defined.
End Total_Category_Univalent_2_1.

Definition fiberwise_local_univalent
           {C : bicat}
           (D : disp_bicat C)
  : UU
  := ∏ (a b : C) (f : C ⟦ a, b ⟧) (aa : D a) (bb : D b)
       (ff : aa -->[ f] bb) (gg : aa -->[ f ] bb),
     isweq (disp_idtoiso_2_1 D (idpath f) ff gg).

Definition fiberwise_local_univalent_is_univalent_2_1
           {C : bicat}
           (D : disp_bicat C)
           (HD : fiberwise_local_univalent D)
  : disp_univalent_2_1 D.
Proof.
  intros x y f g p xx yy ff gg.
  induction p.
  apply HD.
Defined.

Lemma isaprop_disp_left_adjoint_equivalence
      {C : bicat}
      {D : disp_bicat C}
      {a b : C}
      {aa : D a} {bb : D b}
      {f : a --> b}
      (Hf : left_adjoint_equivalence f)
      (ff : aa -->[f] bb)
  : is_univalent_2_1 C →
    disp_univalent_2_1 D →
    isaprop (disp_left_adjoint_equivalence Hf ff).
Proof.
  intros HUC HUD.
  revert Hf. apply hlevel_total2.
  2: { apply hlevelntosn.
       apply isaprop_left_adjoint_equivalence.
       assumption. }
  eapply isofhlevelweqf.
  { apply left_adjoint_equivalence_total_disp_weq. }
  apply isaprop_left_adjoint_equivalence.
  apply total_is_univalent_2_1; assumption.
Defined.

Section Displayed_Global_Univalence.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Definition disp_idtoiso_2_0
             {a b : C}
             (p : a = b)
             (aa : D a) (bb : D b)
             (pp : transportf (λ z, D z) p aa = bb)
    : disp_adjoint_equivalence (idtoiso_2_0 a b p) aa bb.
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
  := ∏ (a : C) (aa bb : D a),
     isweq (disp_idtoiso_2_0 D (idpath a) aa bb).

Definition fiberwise_univalent_2_0_to_disp_univalent_2_0
           {C : bicat}
           (D : disp_bicat C)
  : fiberwise_univalent_2_0 D → disp_univalent_2_0 D.
Proof.
  intros HD.
  intros a b p aa bb.
  induction p.
  exact (HD a aa bb).
Defined.

Section Total_Category_Globally_Univalent.
  Context {C : bicat}.
  Variable (D : disp_bicat C)
           (HC : is_univalent_2_0 C)
           (HD : disp_univalent_2_0 D).
  Local Notation E := (total_bicat D).

  Local Definition path_E_obj
             (x y : C)
             (xx : D x)
             (yy : D y)
    : ((x ,, xx) = (y ,,yy)) ≃ ∑ (p : x = y), transportf _ p xx = yy
    := total2_paths_equiv _ (x ,, xx) (y ,, yy).

  Local Definition path_to_adj_equiv_E
        (x y : C)
        (xx : D x)
        (yy : D y)
    : (∑ (p : x = y), transportf _ p xx = yy)
        ≃
        ∑ (i : adjoint_equivalence x y),
      disp_adjoint_equivalence i xx yy.
  Proof.
    use weqbandf.
    - exact (idtoiso_2_0 x y ,, HC x y).
    - cbn.
      intros p.
      exact (disp_idtoiso_2_0 D p xx yy ,, HD x y p xx yy).
  Defined.

  Definition idtoiso_2_0_alt
             {a b : C}
             (aa : D a) (bb : D b)
    : a,, aa = b,, bb ≃ @adjoint_equivalence E (a,, aa) (b,, bb)
    := ((invweq (adjoint_equivalence_total_disp_weq aa bb))
          ∘ path_to_adj_equiv_E a b aa bb
          ∘ path_E_obj a b aa bb)%weq.

  Definition idtoiso_2_0_is_idtoiso_id_2_0_alt
             (x y : E)
    : @idtoiso_2_0 E x y ~ idtoiso_2_0_alt (pr2 x) (pr2 y).
  Proof.
    intros p.
    induction p.
    use total2_paths_b.
    - reflexivity.
    - use subtypeEquality.
      + intro.
        apply isapropdirprod.
        * apply isapropdirprod ; apply E.
        * apply isapropdirprod ; apply isaprop_is_invertible_2cell.
      + reflexivity.
  Defined.

  Definition total_is_univalent_2_0 : is_univalent_2_0 E.
  Proof.
    intros x y.
    exact (weqhomot (idtoiso_2_0 x y) _ (invhomot (idtoiso_2_0_is_idtoiso_id_2_0_alt x y))).
  Defined.
End Total_Category_Globally_Univalent.

Lemma total_is_univalent_2
      {C : bicat}
      {D: disp_bicat C}
  : disp_univalent_2_0 D →
    disp_univalent_2_1 D →
    is_univalent_2 C →
    is_univalent_2 (total_bicat D).
Proof.
  intros ?? UC.
  split.
  - apply total_is_univalent_2_0. apply UC.
    assumption.
  - apply total_is_univalent_2_1. apply UC.
    assumption.
Defined.
