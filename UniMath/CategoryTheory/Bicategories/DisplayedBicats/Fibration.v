(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition disp_lwhisker_vcomp_alt
           {C : bicat} {D : disp_prebicat C}
           {a b c : C} {f : C⟦a,b⟧} {g h i : C⟦b,c⟧}
           {η : g ==> h} {φ : h ==> i}
           {x : D a} {y : D b} {z : D c} {ff : x -->[f] y}
           {gg : y -->[g] z} {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii)
  : ff ◃◃ (ηη •• φφ)
    =
    transportf (λ α, _ ==>[α] _) (lwhisker_vcomp _ _ _) ((ff ◃◃ ηη) •• (ff ◃◃ φφ)).
Proof.
  refine (!_).
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_lwhisker_vcomp.
Qed.

Definition disp_vcomp_whisker_alt
           {C : bicat} {D : disp_prebicat C}
           {a b c : C} {f g : C⟦a,b⟧} {h i : C⟦b,c⟧}
           (η : f ==> g) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii)
  : (ff ◃◃ φφ) •• (ηη ▹▹ ii)
    =
    transportf (λ α, _ ==>[α] _) (vcomp_whisker _ _) ((ηη ▹▹ hh) •• (gg ◃◃ φφ)).
Proof.
  refine (!_).
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_vcomp_whisker.
Qed.

Definition disp_id2_rwhisker_alt
           {C : bicat} {D : disp_prebicat C}
           {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) (gg : y -->[g] z)
  : transportf (λ α, _ ==>[α] _) (id2_rwhisker _ _) (disp_id2 ff ▹▹ gg)
    =
    disp_id2 (ff ;; gg).
Proof.
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_id2_rwhisker.
Qed.

Section LocalIsoFibration.

  Context {C : bicat}.

  Definition local_iso_cleaving (D : disp_prebicat C)
    : UU
    := ∏ (c c' : C) (f f' : C⟦c,c'⟧)
         (d : D c) (d' : D c')
         (ff' : d -->[f'] d')
         (α : invertible_2cell f f'),
       ∑ ff : d -->[f] d', disp_invertible_2cell α ff ff'.

  Section Projections.

    Context {D : disp_prebicat C} (lic : local_iso_cleaving D)
            {c c' : C} {f f' : C⟦c,c'⟧}
            {d : D c} {d' : D c'}
            (ff' : d -->[f'] d')
            (α : invertible_2cell f f').

    Definition local_iso_cleaving_1cell
      : d -->[f] d'
      := pr1 (lic c c' f f' d d' ff' α).

    Definition disp_local_iso_cleaving_invertible_2cell
      : disp_invertible_2cell α local_iso_cleaving_1cell ff'
      := pr2 (lic c c' f f' d d' ff' α).

  End Projections.

  Section Discrete_Fiber.

    Variable (D : disp_prebicat C) (h : local_iso_cleaving D) (c : C).

    Definition discrete_fiber_ob_mor : precategory_ob_mor.
    Proof.
      use tpair.
      - exact (D c).
      - cbn. exact (λ (d : D c) (d' : D c), d -->[identity c] d').
    Defined.

    Definition idempunitor : invertible_2cell (identity c) (identity c · identity c).
    Proof.
      exists (linvunitor (identity c)).
      apply is_invertible_2cell_linvunitor.
    Defined.

    Definition discrete_fiber_precategory_data : precategory_data.
    Proof.
      exists discrete_fiber_ob_mor.
      split; cbn.
      - intro d. exact (id_disp d).
      - intros x y z ff gg.
        use (local_iso_cleaving_1cell h).
        + exact (identity c · identity c).
        + exact (ff ;; gg).
        + exact idempunitor.
    Defined.

    Definition discrete_fiber_1_id_comp_cells : prebicat_1_id_comp_cells.
    Proof.
      exists discrete_fiber_precategory_data.
      red. cbn. intros d d' f f'.
      exact (f ==>[id2 (identity c)] f').
    Defined.

    Definition discrete_fiber_data : prebicat_data.
    Proof.
      exists discrete_fiber_1_id_comp_cells.
      repeat split; cbn.
      - intros. exact (disp_id2 _).
      - intros d d' ff.
        set (PP := disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) idempunitor).
        set (RR := PP •• disp_lunitor ff).
        assert (Heq : idempunitor • lunitor (identity c) = id2 (identity c)).
        { abstract (apply linvunitor_lunitor). }
        exact (transportf (λ x, _ ==>[x] _) Heq RR).
      - intros d d' ff.
        assert (Heq : idempunitor • runitor (identity c) = id2 (identity c)).
        { abstract (cbn
                    ; rewrite <- lunitor_runitor_identity, linvunitor_lunitor
                    ; reflexivity).
        }
        set (PP := disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') idempunitor).
        exact (transportf (λ x, _ ==>[x] _) Heq (PP •• disp_runitor ff)).
      - intros d d' ff.
        set (PP := disp_inv_cell
                     (disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) idempunitor)).
        assert (Heq : linvunitor (identity c) • idempunitor^-1 = id2 (identity c)).
        { abstract (apply linvunitor_lunitor). }
        exact (transportf (λ x, _ ==>[x] _) Heq (disp_linvunitor ff •• PP)).
      - cbn. intros d d' ff.
        set (PP := disp_inv_cell
                     (disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') idempunitor)).
        assert (Heq : rinvunitor (identity c) • idempunitor^-1 = id2 (identity c)).
        { unfold idempunitor. cbn.
          abstract (rewrite lunitor_runitor_identity, rinvunitor_runitor
                    ; reflexivity).
        }
        exact (transportf (λ x, _ ==>[x] _) Heq (disp_rinvunitor ff •• PP)).
      - intros d0 d1 d2 d3 ff gg hh.
        assert ((idempunitor • (idempunitor ▹ identity c)) • rassociator _ _ _ • ((identity c ◃ lunitor _) • lunitor _) = id2 _) as Heq.
        {
          abstract
            (cbn ;
             rewrite !lwhisker_hcomp, !rwhisker_hcomp ;
             rewrite lunitor_V_id_is_left_unit_V_id ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite <- triangle_l_inv ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite lassociator_rassociator, id2_left ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite <- hcomp_vcomp ;
             rewrite id2_left, linvunitor_lunitor ;
             rewrite hcomp_identity, id2_left ;
             rewrite <- lunitor_V_id_is_left_unit_V_id ;
             rewrite linvunitor_lunitor ;
             reflexivity
            ).
        }
        refine (transportf (λ z, _ ==>[ z ] _) Heq _).
        cbn.
        refine (_ •• disp_rassociator ff gg hh •• _).
        + refine (disp_local_iso_cleaving_invertible_2cell h (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh) idempunitor •• _).
          refine (disp_rwhisker _ _).
          exact (disp_local_iso_cleaving_invertible_2cell h (ff ;; gg) idempunitor).
        + refine (_ •• _).
          * refine (disp_lwhisker _ _).
            exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (gg ;; hh) idempunitor)).
          * exact (disp_inv_cell ((disp_local_iso_cleaving_invertible_2cell h (ff;;local_iso_cleaving_1cell h (gg;; hh) idempunitor) idempunitor))).
      - intros d0 d1 d2 d3 ff gg hh.
        assert ((idempunitor • (identity c ◃ idempunitor)) • lassociator _ _ _ • ((lunitor _ ▹ identity c) • lunitor _) = id2 _) as Heq.
        {
          abstract
            (cbn ;
             rewrite !lwhisker_hcomp, !rwhisker_hcomp ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite triangle_r_inv ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator, id2_left ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite <- hcomp_vcomp ;
             rewrite <- lunitor_V_id_is_left_unit_V_id ;
             rewrite id2_left, linvunitor_lunitor ;
             rewrite hcomp_identity, id2_left ;
             apply linvunitor_lunitor
            ).
        }
        refine (transportf (λ z, _ ==>[ z ] _) Heq _).
        cbn.
        refine (_ •• disp_lassociator ff gg hh •• _).
        + refine (_ •• _).
          * exact (disp_local_iso_cleaving_invertible_2cell h (ff;;local_iso_cleaving_1cell h (gg;; hh) idempunitor) idempunitor).
          * refine (disp_lwhisker _ _).
            exact (disp_local_iso_cleaving_invertible_2cell h (gg ;; hh) idempunitor).
        + refine (_ •• _).
          * refine (disp_rwhisker _ _).
            exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (ff ;; gg) idempunitor)).
          * exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh) idempunitor)).
      - intros a b f1 f2 f3 x y.
        exact (transportf (λ z, _ ==>[ z ] _) (id2_left _) (x •• y)).
      - intros a1 a2 a3 f g1 g2 x.
        assert (linvunitor _ • (identity c ◃ id2 _) • lunitor _ = id2 (identity c)) as Heq.
        {
          abstract (rewrite lwhisker_id2 ;
                    rewrite id2_right ;
                    apply linvunitor_lunitor).
        }
        refine (transportf (λ z, _ ==>[ z ] _) Heq _).
        refine (_ •• (f ◃◃ x) •• _).
        + exact (disp_local_iso_cleaving_invertible_2cell h (f ;; g1) idempunitor).
        + exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (f ;; g2) idempunitor)).
      - intros a1 a2 a3 f1 f2 g x.
        assert (linvunitor _ • (id2 _ ▹ identity _) • lunitor _ = id2 (identity c)) as Heq.
        {
          abstract (rewrite id2_rwhisker ;
                    rewrite id2_right ;
                    apply linvunitor_lunitor).
        }
        refine (transportf (λ z, _ ==>[ z ] _) Heq _).
        refine (_ •• (x ▹▹ g) •• _).
        + exact (disp_local_iso_cleaving_invertible_2cell h (f1 ;; g) idempunitor).
        + exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (f2 ;; g) idempunitor)).
    Defined.

    Local Arguments transportf {_} {_} {_} {_} {_} _.
    Local Arguments transportb {_} {_} {_} {_} {_} _.

    Local Definition discete_fiber_data_laws_vcomp_left
      :  ∏ (a b : discrete_fiber_data)
           (f g : discrete_fiber_data ⟦ a, b ⟧)
           (x : f ==> g),
         id₂ f • x = x.
    Proof.
      intros a b f g x ; cbn.
      rewrite disp_id2_left.
      rewrite transportfbinv.
      reflexivity.
    Qed.

    Local Definition discete_fiber_data_laws_vcomp_right
      :  ∏ (a b : discrete_fiber_data)
           (f g : discrete_fiber_data ⟦ a, b ⟧)
           (x : f ==> g),
         x • id₂ g = x.
    Proof.
      intros a b f g x ; cbn.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite transportf_set.
      - reflexivity.
      - apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_vcomp_assoc
      : ∏ (a b : discrete_fiber_data)
          (f₁ f₂ f₃ f₄ : discrete_fiber_data ⟦ a, b ⟧)
          (x : f₁ ==> f₂)
          (y : f₂ ==> f₃)
          (z : f₃ ==> f₄),
        x • (y • z) = (x • y) • z.
    Proof.
      intros a b f₁ f₂ f₃ f₄ x y z ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_vassocr.
      rewrite disp_mor_transportf_postwhisker.
      unfold transportb.
      rewrite !transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, f₁ ==>[ α] f₄)).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_rwhisker_id2
      : ∏ (a₁ a₂ a₃ : discrete_fiber_data)
          (f : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
          (g : discrete_fiber_data ⟦ a₂, a₃ ⟧),
        f ◃ id₂ g = id₂ (f · g).
    Proof.
      intros a₁ a₂ a₃ f g ; cbn.
      rewrite disp_lwhisker_id2.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      apply (@transportf_transpose_alt _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      refine (disp_vcomp_rinv
                (disp_local_iso_cleaving_invertible_2cell h (f;; g) idempunitor)
                @ _).
      unfold transportb.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_id2_lwhisker
      : ∏ (a₁ a₂ a₃ : discrete_fiber_data)
          (f : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
          (g : discrete_fiber_data ⟦ a₂ , a₃ ⟧),
        id₂ f ▹ g = id₂ (f · g).
    Proof.
      intros a₁ a₂ a₃ f g ; cbn.
      rewrite disp_id2_rwhisker.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      apply (@transportf_transpose_alt _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      refine (disp_vcomp_rinv
                (disp_local_iso_cleaving_invertible_2cell h (f;; g) idempunitor)
                @ _).
      unfold transportb.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_vcomp_lwhisker
      :  ∏ (a₁ a₂ a₃ : discrete_fiber_data)
           (f : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (g₁ g₂ g₃ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (x : g₁ ==> g₂)
           (y : g₂ ==> g₃),
         (f ◃ x) • (f ◃ y) = f ◃ (x • y).
    Proof.
      intros a₁ a₂ a₃ f g₁ g₂ g₃ x y ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      rewrite (maponpaths (λ z, _ •• z) (disp_vassocr _ _ _)).
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite (maponpaths (λ z, (_ •• _) •• (z •• _)) (disp_vassocr _ _ _)).
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        refine (maponpaths (λ z, (_ •• _) •• ((z •• _) •• _)) _).
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (f;; g₂) idempunitor)).
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      unfold transportb.
      rewrite transport_f_f.
      rewrite (maponpaths (λ z, _ •• z) (disp_vassocr _ _ _)).
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply disp_lwhisker_vcomp.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_rwhisker_transport_right.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      unfold transportb.
      rewrite transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_vcomp_rwhisker
      : ∏ (a₁ a₂ a₃ : discrete_fiber_data)
          (f₁ f₂ f₃ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
          (g : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
          (x : f₁ ==> f₂)
          (y : f₂ ==> f₃),
        (x ▹ g) • (y ▹ g) = (x • y) ▹ g.
    Proof.
      intros a₁ a₂ a₃ f₁ f₂ f₃ f₄ x y ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_rwhisker_transport_left.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite !disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (f₂;; f₄) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      do 2 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocl.
        apply maponpaths.
        apply maponpaths.
        apply disp_rwhisker_vcomp.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      refine (!_).
    Admitted.

    Local Definition discrete_fiber_data_laws_vcomp_lunitor
      : ∏ (a b : discrete_fiber_data)
          (f g : discrete_fiber_data ⟦ a, b ⟧)
          (x : f ==> g),
        (id₁ a ◃ x) • lunitor g = lunitor f • x.
    Proof.
      intros a b f g x ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite !disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (id_disp a;; g) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply disp_vcomp_lunitor.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_vassocr.
      unfold transportb.
      rewrite transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_vcomp_runitor
      : ∏ (a b : discrete_fiber_data)
          (f g : discrete_fiber_data ⟦ a, b ⟧)
          (x : f ==> g),
        (x ▹ id₁ b) • runitor g = runitor f • x.
    Proof.
      intros a b f g x ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite !disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (g;;id_disp b) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply disp_vcomp_runitor.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_vassocr.
      unfold transportb.
      rewrite transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_lwhisker_lwhisker
      : ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data)
          (f₁ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
          (f₂ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
          (f₃ f₄ : discrete_fiber_data ⟦ a₃ , a₄ ⟧)
          (x : f₃ ==> f₄),
        (f₁ ◃ (f₂ ◃ x)) • lassociator f₁ f₂ f₄
        =
        lassociator f₁ f₂ f₃ • (f₁ · f₂ ◃ x).
    Proof.
      intros a₁ a₂ a₃ a₄ f₁ f₂ g₁ g₂ x ; cbn.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_rwhisker_transport_right.
      rewrite disp_mor_transportf_prewhisker.
      do 2 rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        rewrite !disp_vassocr.
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell
                    h
                    (f₁;; local_iso_cleaving_1cell h (f₂;; g₂) idempunitor) idempunitor)).
      }
      unfold transportb.
      do 9 rewrite disp_mor_transportf_postwhisker.
      do 5 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        do 3 apply maponpaths_2.
        apply disp_id2_left.
      }
      unfold transportb.
      do 3 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        apply maponpaths.
        apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_lwhisker_vcomp.
        apply maponpaths.
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell h (f₂;; g₂) idempunitor)).
      }
      unfold transportb.
      do 6 rewrite disp_mor_transportf_postwhisker.
      do 5 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        do 3 apply maponpaths_2.
        do 2 apply maponpaths.
        apply disp_id2_right.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_rwhisker_transport_right.
      do 3 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      refine (!(_ @ _)).
      {
        apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell
                    h
                    (local_iso_cleaving_1cell h (f₁;; f₂) idempunitor;; g₁)
                    idempunitor)).
      }
      unfold transportb.
      do 3 rewrite disp_mor_transportf_postwhisker.
      do 3 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        do 2 apply maponpaths.
        apply disp_id2_right.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      do 2 rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      refine (!(_ @ _)).
      {
        do 2 apply maponpaths.
        do 3 apply maponpaths_2.
        apply disp_lwhisker_vcomp_alt.
      }
      do 3 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        do 2 apply maponpaths_2.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply disp_lwhisker_lwhisker.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      do 2 rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply disp_vcomp_whisker_alt.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite !disp_vassocr.
      unfold transportb.
      do 3 rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Admitted.

    Local Definition discrete_fiber_data_vcomp_whisker
      :  ∏ (a₁ a₂ a₃ : discrete_fiber_data)
           (f₁ f₂ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (g₁ g₂ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (x : f₁ ==> f₂) (y : g₁ ==> g₂),
         (x ▹ g₁) • (f₂ ◃ y) = (f₁ ◃ y) • (x ▹ g₂).
    Proof.
      intros a₁ a₂ a₃ f₁ f₂ g₁ g₂ x y ; cbn.
      rewrite !disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite !disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell h (f₂;; g₁) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        apply disp_vcomp_whisker.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      refine (!(_ @ _)).
      {
        apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell h (f₁;; g₂) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply disp_vassocl.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_lunitor_linvunitor
      :  ∏ (a b : discrete_fiber_data)
           (f : discrete_fiber_data ⟦ a, b ⟧),
         lunitor f • linvunitor f = id₂ (id₁ a · f).
    Proof.
      intros a b f ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths, maponpaths_2.
        apply disp_lunitor_linvunitor.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_vcomp_rinv (disp_local_iso_cleaving_invertible_2cell h (id_disp a;; f) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_linvunitor_lunitor
      :  ∏ (a b : discrete_fiber_data)
           (f : discrete_fiber_data ⟦ a, b ⟧),
         linvunitor f • lunitor f = id₂ f.
    Proof.
      intros a b f ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths, maponpaths_2.
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (id_disp a;; f) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply disp_linvunitor_lunitor.
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_runitor_rinvunitor
      :  ∏ (a b : discrete_fiber_data)
           (f : discrete_fiber_data ⟦ a, b ⟧),
         runitor f • rinvunitor f = id₂ (f · id₁ b).
    Proof.
      intros a b f ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths, maponpaths_2.
        apply disp_runitor_rinvunitor.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_vcomp_rinv
                 (disp_local_iso_cleaving_invertible_2cell h (f ;; id_disp b)
                                                           idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.

    Local Definition discete_fiber_data_laws
      :  ∏ (a b : discrete_fiber_data)
           (f : discrete_fiber_data ⟦ a, b ⟧),
         rinvunitor f • runitor f = id₂ f.
    Proof.
      intros a b f ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths, maponpaths_2.
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (f ;; id_disp b) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply disp_rinvunitor_runitor.
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.

    Local Definition discrete_fiber_data_laws_lassociator_rassociator
      :  ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data)
           (f₁ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (f₂ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (f₃ : discrete_fiber_data ⟦ a₃ , a₄ ⟧),
         lassociator f₁ f₂ f₃ • rassociator f₁ f₂ f₃
         =
         id₂ (f₁ · (f₂ · f₃)).
    Proof.
      intros a₁ a₂ a₃ a₄ f₁ f₂ f₃ ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell
                    h
                    (local_iso_cleaving_1cell h (f₁;; f₂) idempunitor;; f₃) idempunitor)).
      }
      unfold transportb.
      do 3 rewrite disp_mor_transportf_prewhisker.
      do 6 rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        do 2 apply maponpaths_2.
        apply disp_id2_left.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 3 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_rwhisker_vcomp.
        do 2 apply maponpaths.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell h (f₁;; f₂) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      do 3 rewrite disp_mor_transportf_postwhisker.
      do 6 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        do 2 apply maponpaths_2.
        apply disp_rwhisker_transport_left_new.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        do 2 apply maponpaths_2.
        apply disp_id2_rwhisker.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths, maponpaths_2.
        apply disp_lassociator_rassociator.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_lwhisker_vcomp.
        do 2 apply maponpaths.
        apply (disp_vcomp_rinv
                 (disp_local_iso_cleaving_invertible_2cell h (f₂;; f₃) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        rewrite disp_rwhisker_transport_right.
        apply maponpaths.
        apply disp_lwhisker_id2.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_vcomp_rinv (disp_local_iso_cleaving_invertible_2cell h (f₁;; local_iso_cleaving_1cell h (f₂;; f₃) idempunitor) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Admitted.

    Local Definition discrete_fiber_data_laws_rassociator_lassociator
      :  ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data)
           (f₁ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (f₂ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (f₃ : discrete_fiber_data ⟦ a₃ , a₄ ⟧),
         rassociator f₁ f₂ f₃ • lassociator f₁ f₂ f₃
         =
         id₂ (f₁ · f₂ · f₃).
    Proof.
      intros a₁ a₂ a₃ a₄ f₁ f₂ f₃ ; cbn.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell
                    h
                    (f₁;; local_iso_cleaving_1cell h (f₂;; f₃) idempunitor)
                    idempunitor)).
      }
      unfold transportb.
      do 3 rewrite disp_mor_transportf_prewhisker.
      do 6 rewrite disp_mor_transportf_postwhisker.
      rewrite !transport_f_f.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        do 2 apply maponpaths_2.
        apply disp_id2_left.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 3 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_lwhisker_vcomp.
        do 2 apply maponpaths.
        apply (disp_vcomp_linv
                 (disp_local_iso_cleaving_invertible_2cell h (f₂;; f₃) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      do 3 rewrite disp_mor_transportf_postwhisker.
      do 6 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        do 2 apply maponpaths_2.
        apply disp_rwhisker_transport_right.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        do 2 apply maponpaths_2.
        apply disp_lwhisker_id2.
      }
      unfold transportb.
      do 2 rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths, maponpaths_2.
        apply disp_rassociator_lassociator.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        rewrite disp_rwhisker_vcomp.
        do 2 apply maponpaths.
        apply (disp_vcomp_rinv
                 (disp_local_iso_cleaving_invertible_2cell h (f₁;; f₂) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      do 2 rewrite disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        rewrite disp_rwhisker_transport_left_new.
        apply maponpaths.
        apply disp_id2_rwhisker.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply disp_id2_left.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_vcomp_rinv (disp_local_iso_cleaving_invertible_2cell h (local_iso_cleaving_1cell h (f₁;; f₂) idempunitor;; f₃) idempunitor)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Admitted.

    Definition discrete_fiber_data_laws : prebicat_laws discrete_fiber_data.
    Proof.
      repeat split.
      - exact discete_fiber_data_laws_vcomp_left.
      - exact discete_fiber_data_laws_vcomp_right.
      - exact discrete_fiber_data_laws_vcomp_assoc.
      - exact discrete_fiber_data_laws_rwhisker_id2.
      - exact discrete_fiber_data_laws_id2_lwhisker.
      - exact discrete_fiber_data_laws_vcomp_lwhisker.
      - exact discrete_fiber_data_laws_vcomp_rwhisker.
      - exact discrete_fiber_data_laws_vcomp_lunitor.
      - exact discrete_fiber_data_laws_vcomp_runitor.
      - exact discrete_fiber_data_laws_lwhisker_lwhisker.
      - admit.
      - admit.
      - exact discrete_fiber_data_vcomp_whisker.
      - exact discrete_fiber_data_laws_lunitor_linvunitor.
      - exact discrete_fiber_data_laws_linvunitor_lunitor.
      - exact discrete_fiber_data_laws_runitor_rinvunitor.
      - exact discete_fiber_data_laws.
      - exact discrete_fiber_data_laws_lassociator_rassociator.
      - exact discrete_fiber_data_laws_rassociator_lassociator.
      - intros a₁ a₂ a₃ f₁ f₂ ; cbn.
        admit.
      - intros a b f g x.
        admit.
    Admitted.

    Definition discrete_fiber : prebicat.
    Proof.
      use tpair.
      - exact discrete_fiber_data.
      - exact discrete_fiber_data_laws.
    Defined.

  End Discrete_Fiber.

End LocalIsoFibration.
