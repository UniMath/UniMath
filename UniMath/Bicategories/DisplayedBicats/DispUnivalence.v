(* *********************************************************************************** *)
(** * Internal adjunction in displayed bicategories

    Benedikt Ahrens, Marco Maggesi
    April 2018                                                                         *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
(* For showing that the being a displayed adjoint equivalence is a proposition *)
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Export UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Export UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Export UniMath.Bicategories.DisplayedBicats.DispAdjunctions.

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

  Definition disp_isotoid_2_1
             (HD : disp_univalent_2_1)
             {a b : C}
             {f g : C⟦a, b⟧}
             (p : f = g)
             {aa : D a} {bb : D b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
             (pp : disp_invertible_2cell (idtoiso_2_1 f g p) ff gg)
    : transportf (λ z, _ -->[ z ] _) p ff = gg
    := invmap (make_weq _ (HD a b f g p aa bb ff gg)) pp.
End Displayed_Local_Univalence.

(** Some laws of `disp_idtoiso_2_1` *)
Definition disp_1cell_transport_rwhisker
           {B : bicat}
           {D : disp_bicat B}
           {b₁ b₂ b₃ : B}
           {h : b₁ --> b₂}
           {f : b₂ --> b₃}
           {g : b₁ --> b₃}
           {α : h · f ==> g}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {bb₃ : D b₃}
           (ff : bb₂ -->[ f ] bb₃)
           (gg : bb₁ -->[ g ] bb₃)
           {hh₁ hh₂ : bb₁ -->[ h] bb₂}
           (p : hh₁ = hh₂)
           (αα : hh₁ ;; ff ==>[ α] gg)
  : transportf
      (λ (z : bb₁ -->[ h ] bb₂), z ;; ff ==>[ α ] gg)
      p
      αα
    =
    transportf
      (λ z, _ ==>[ z ] _)
      (maponpaths (λ z, z • _) (id2_rwhisker _ _) @ id2_left _)
      ((disp_idtoiso_2_1 _ (idpath _) _ _ (!p) ▹▹ ff) •• αα).
Proof.
  induction p ; cbn.
  cbn.
  rewrite disp_id2_rwhisker.
  unfold transportb.
  rewrite disp_mor_transportf_postwhisker.
  rewrite disp_id2_left.
  unfold transportb.
  rewrite !transport_f_f.
  refine (!_).
  use (transportf_set (λ z : h · f ==> g, hh₁ ;; ff ==>[ z ] gg)).
  apply cellset_property.
Qed.

Definition disp_idtoiso_2_1_inv
           {B : bicat}
           {D : disp_bicat B}
           {b₁ b₂ : B}
           {f : b₁ --> b₂}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           (ff₁ ff₂ : bb₁ -->[ f ] bb₂)
           (p : ff₁ = ff₂)
  : pr1 (disp_idtoiso_2_1 _ (idpath _) _ _ (!p))
    =
    disp_inv_cell (disp_idtoiso_2_1 _ (idpath _) _ _ p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition disp_idtoiso_isotoid_2_1
           {B : bicat}
           {D : disp_bicat B}
           (HD_2_1 : disp_univalent_2_1 D)
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           (p : f = g)
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {ff : bb₁ -->[ f ] bb₂}
           {gg : bb₁ -->[ g ] bb₂}
           (α : disp_invertible_2cell (idtoiso_2_1 f g p) ff gg)
  : disp_idtoiso_2_1
      _ p ff gg
      (disp_isotoid_2_1
         _ HD_2_1
         p ff gg
         α)
    =
    α.
Proof.
  exact (homotweqinvweq
           (make_weq _ (HD_2_1 b₁ b₂ f g p bb₁ bb₂ ff gg))
           α).
Qed.

Definition disp_isotoid_idtoiso_2_1
           {B : bicat}
           {D : disp_bicat B}
           (HD_2_1 : disp_univalent_2_1 D)
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           (p : f = g)
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {ff : bb₁ -->[ f ] bb₂}
           {gg : bb₁ -->[ g ] bb₂}
           (pp : transportf (λ z, bb₁ -->[ z] bb₂) p ff = gg)
  : disp_isotoid_2_1
      _ HD_2_1
      p ff gg
      (disp_idtoiso_2_1
         _ p ff gg
         pp)
    =
    pp.
Proof.
  exact (homotinvweqweq
           (make_weq _ (HD_2_1 b₁ b₂ f g p bb₁ bb₂ ff gg))
           pp).
Qed.

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

Definition disp_isotoid_2_0
           {B : bicat}
           {D : disp_bicat B}
           (HD_2_0 : disp_univalent_2_0 D)
           {x : B}
           {xx yy : D x}
           (ee : disp_adjoint_equivalence
                   (internal_adjoint_equivalence_identity x)
                   xx
                   yy)
  : xx = yy
  := invmap
       (make_weq _ (HD_2_0 x x (idpath _) xx yy))
       ee.

Definition disp_idtoiso_2_0_isotoid_2_0
           {B : bicat}
           {D : disp_bicat B}
           (HD_2_0 : disp_univalent_2_0 D)
           {x : B}
           {xx yy : D x}
           (ee : disp_adjoint_equivalence
                   (internal_adjoint_equivalence_identity x)
                   xx
                   yy)
  : disp_idtoiso_2_0 D (idpath _) xx yy (disp_isotoid_2_0 HD_2_0 ee)
    =
    ee.
Proof.
  exact (homotweqinvweq (make_weq _ (HD_2_0 x x (idpath _) xx yy)) ee).
Defined.

Definition disp_isotoid_2_0_idtoiso_2_0
           {B : bicat}
           {D : disp_bicat B}
           (HD_2_0 : disp_univalent_2_0 D)
           {x : B}
           {xx yy : D x}
           (p : xx = yy)
  : disp_isotoid_2_0 HD_2_0 (disp_idtoiso_2_0 _ (idpath _) xx yy p) = p.
Proof.
  exact (homotinvweqweq (make_weq _ (HD_2_0 x x (idpath _) xx yy)) p).
Defined.

Definition disp_J_2_0_help_on_paths
           {B : bicat}
           {D : disp_bicat B}
           (P : ∏ (x y : B)
                  (f : adjoint_equivalence x y)
                  (xx : D x) (yy : D y),
                disp_adjoint_equivalence f xx yy → UU)
           (P_id : ∏ (x : B)
                     (xx : D x),
                   P x x
                     (internal_adjoint_equivalence_identity x)
                     xx xx
                     (disp_identity_adjoint_equivalence xx))
           {x : B}
           {xx : D x} {yy : D x}
           (p : xx = yy)
  : P x x
      (internal_adjoint_equivalence_identity x)
      xx yy
      (disp_idtoiso_2_0 D (idpath x) xx yy p).
Proof.
  induction p.
  apply P_id.
Defined.

Definition disp_J_2_0_help
           {B : bicat}
           {D : disp_bicat B}
           (HD_2_0 : disp_univalent_2_0 D)
           (P : ∏ (x y : B)
                  (f : adjoint_equivalence x y)
                  (xx : D x) (yy : D y),
                disp_adjoint_equivalence f xx yy → UU)
           (P_id : ∏ (x : B)
                     (xx : D x),
                   P x x
                     (internal_adjoint_equivalence_identity x)
                     xx xx
                     (disp_identity_adjoint_equivalence xx))
           {x : B}
           {xx : D x} {yy : D x}
           (ff : disp_adjoint_equivalence
                   (internal_adjoint_equivalence_identity x)
                   xx
                   yy)
  : P x x (internal_adjoint_equivalence_identity x) xx yy ff.
Proof.
  pose (disp_J_2_0_help_on_paths P P_id (disp_isotoid_2_0 HD_2_0 ff)).
  refine (transportf
            (P x x _ xx yy)
            _
            (disp_J_2_0_help_on_paths P P_id (disp_isotoid_2_0 HD_2_0 ff))).
  apply disp_idtoiso_2_0_isotoid_2_0.
Defined.

Definition disp_J_2_0
           {B : bicat}
           {D : disp_bicat B}
           (HB_2_0 : is_univalent_2_0 B)
           (HD_2_0 : disp_univalent_2_0 D)
           (P : ∏ (x y : B)
                  (f : adjoint_equivalence x y)
                  (xx : D x) (yy : D y),
                disp_adjoint_equivalence f xx yy → UU)
           (P_id : ∏ (x : B)
                     (xx : D x),
                   P x x
                     (internal_adjoint_equivalence_identity x)
                     xx xx
                     (disp_identity_adjoint_equivalence xx))
           {x y : B}
           {f : adjoint_equivalence x y}
           {xx : D x} {yy : D y}
           (ff : disp_adjoint_equivalence f xx yy)
  : P x y f xx yy ff.
Proof.
  revert x y f xx yy ff.
  use (J_2_0 HB_2_0).
  intros x xx yy ff.
  exact (disp_J_2_0_help HD_2_0 P P_id ff).
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
    - use subtypePath.
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

Section Disp_Univalent_2.

  Context {C : bicat}.

  Definition disp_univalent_2 (D : disp_bicat C)
    : UU
    := disp_univalent_2_0 D × disp_univalent_2_1 D.

  Definition make_disp_univalent_2 {D : disp_bicat C}
             (univ_2_0 : disp_univalent_2_0 D)
             (univ_2_1 : disp_univalent_2_1 D)
    : disp_univalent_2 D
    := make_dirprod univ_2_0 univ_2_1.

  Definition disp_univalent_2_0_of_2 {D : disp_bicat C}
             (univ_2 : disp_univalent_2 D)
    : disp_univalent_2_0 D
    := pr1 univ_2.

  Definition disp_univalent_2_1_of_2 {D : disp_bicat C}
             (univ_2 : disp_univalent_2 D)
    : disp_univalent_2_1 D
    := pr2 univ_2.

End Disp_Univalent_2.

Lemma total_is_univalent_2
      {C : bicat}
      {D: disp_bicat C}
  : disp_univalent_2 D →
    is_univalent_2 C →
    is_univalent_2 (total_bicat D).
Proof.
  intros UD UC.
  split.
  - apply total_is_univalent_2_0. apply UC.
    apply disp_univalent_2_0_of_2. assumption.
  - apply total_is_univalent_2_1. apply UC.
    apply disp_univalent_2_1_of_2. assumption.
Defined.

(** Displayed local univalence corresponds with the expected local condition *)
Section DispLocallyUnivalent.
  Context {B : bicat}
          (D : disp_bicat B)
          {x y : B}
          {f : x --> y}
          {xx : D x}
          {yy : D y}
          (ff₁ ff₂ : xx -->[ f ] yy).

  Definition disp_inv2cell_to_disp_z_iso
    : disp_invertible_2cell (id2_invertible_2cell f) ff₁ ff₂
      →
      @z_iso_disp _ (disp_hom xx yy) _ _ (identity_z_iso _) ff₁ ff₂.
  Proof.
    intro α.
    simple refine (@make_z_iso_disp _ (disp_hom xx yy) _ _ _ _ _ _ _).
    - exact (pr1 α).
    - simple refine (_ ,, _ ,, _).
      + exact (disp_inv_cell α).
      + abstract
          (refine (disp_vcomp_linv α @ _) ; cbn ;
           apply maponpaths_2 ;
           apply cellset_property).
      + abstract
          (refine (disp_vcomp_rinv α @ _) ; cbn ;
           apply maponpaths_2 ;
           apply cellset_property).
  Defined.

  Definition disp_z_iso_to_disp_inv2cell
    : @z_iso_disp _ (disp_hom xx yy) _ _ (identity_z_iso _) ff₁ ff₂
      →
      disp_invertible_2cell (id2_invertible_2cell f) ff₁ ff₂.
  Proof.
    intro α.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr1 α).
    - exact (inv_mor_disp_from_z_iso α).
    - abstract
        (cbn ;
         refine (pr222 α @ _) ;
         apply maponpaths_2 ;
         apply cellset_property).
    - abstract
        (cbn ;
         refine (pr122 α @ _) ;
         apply maponpaths_2 ;
         apply cellset_property).
  Defined.

  Definition disp_inv2cell_weq_disp_z_iso
    : disp_invertible_2cell (id2_invertible_2cell f) ff₁ ff₂
      ≃
      @z_iso_disp _ (disp_hom xx yy) _ _ (identity_z_iso _) ff₁ ff₂.
  Proof.
    use make_weq.
    - exact disp_inv2cell_to_disp_z_iso.
    - use isweq_iso.
      + exact disp_z_iso_to_disp_inv2cell.
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
           apply idpath).
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
           apply idpath).
  Defined.
End DispLocallyUnivalent.

Definition is_univalent_disp_disp_hom
           {B : bicat}
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
           {x y : B}
           (xx : D x)
           (yy : D y)
  : is_univalent_disp (disp_hom xx yy).
Proof.
  intros f g p ff gg.
  induction p.
  use weqhomot.
  - exact (disp_inv2cell_weq_disp_z_iso D _ _
           ∘ make_weq _ (HD x y f f (idpath _) xx yy ff gg))%weq.
  - abstract
      (intro p ;
       induction p ;
       use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
       apply idpath).
Defined.
