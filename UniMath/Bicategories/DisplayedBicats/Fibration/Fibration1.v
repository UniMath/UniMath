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
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DisplayedBicats.FiberCategory.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section LocalIsoFibration.
  Context {C : bicat}
          (D : disp_bicat C)
          (h : local_iso_cleaving D)
          (c : C).

  Section Discrete_Fiber.

    Definition discrete_fiber_1_id_comp_cells : prebicat_1_id_comp_cells.
    Proof.
      exists (discrete_fiber_precategory_data D h c).
      red. cbn. intros d d' f f'.
      exact (f ==>[id2 (identity c)] f').
    Defined.

    Definition discrete_fiber_data : prebicat_data.
    Proof.
      exists discrete_fiber_1_id_comp_cells.
      repeat split; cbn.
      - intros. exact (disp_id2 _).
      - intros d d' ff.
        set (PP := disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) (idempunitor c)).
        set (RR := PP •• disp_lunitor ff).
        assert (Heq : (idempunitor c) • lunitor (identity c) = id2 (identity c)).
        { abstract (apply linvunitor_lunitor). }
        exact (transportf (λ x, _ ==>[x] _) Heq RR).
      - intros d d' ff.
        assert (Heq : (idempunitor c) • runitor (identity c) = id2 (identity c)).
        { abstract (cbn
                    ; rewrite <- lunitor_runitor_identity, linvunitor_lunitor
                    ; reflexivity).
        }
        set (PP := disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') (idempunitor c)).
        exact (transportf (λ x, _ ==>[x] _) Heq (PP •• disp_runitor ff)).
      - intros d d' ff.
        set (PP := disp_inv_cell
                     (disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) (idempunitor c))).
        assert (Heq : linvunitor (identity c) • (idempunitor c)^-1 = id2 (identity c)).
        { abstract (apply linvunitor_lunitor). }
        exact (transportf (λ x, _ ==>[x] _) Heq (disp_linvunitor ff •• PP)).
      - cbn. intros d d' ff.
        set (PP := disp_inv_cell
                     (disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') (idempunitor c))).
        assert (Heq : rinvunitor (identity c) • (idempunitor c)^-1 = id2 (identity c)).
        { unfold idempunitor. cbn.
          abstract (rewrite lunitor_runitor_identity, rinvunitor_runitor
                    ; reflexivity).
        }
        exact (transportf (λ x, _ ==>[x] _) Heq (disp_rinvunitor ff •• PP)).
      - intros d0 d1 d2 d3 ff gg hh.
        assert (((idempunitor c) • ((idempunitor c) ▹ identity c)) • rassociator _ _ _ • ((identity c ◃ lunitor _) • lunitor _) = id2 _) as Heq.
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
        + refine (disp_local_iso_cleaving_invertible_2cell h (local_iso_cleaving_1cell h (ff;; gg) (idempunitor c);; hh) (idempunitor c) •• _).
          refine (disp_rwhisker _ _).
          exact (disp_local_iso_cleaving_invertible_2cell h (ff ;; gg) (idempunitor c)).
        + refine (_ •• _).
          * refine (disp_lwhisker _ _).
            exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (gg ;; hh) (idempunitor c))).
          * exact (disp_inv_cell ((disp_local_iso_cleaving_invertible_2cell h (ff;;local_iso_cleaving_1cell h (gg;; hh) (idempunitor c)) (idempunitor c)))).
      - intros d0 d1 d2 d3 ff gg hh.
        assert (((idempunitor c) • (identity c ◃ (idempunitor c))) • lassociator _ _ _ • ((lunitor _ ▹ identity c) • lunitor _) = id2 _) as Heq.
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
          * exact (disp_local_iso_cleaving_invertible_2cell h (ff;;local_iso_cleaving_1cell h (gg;; hh) (idempunitor c)) (idempunitor c)).
          * refine (disp_lwhisker _ _).
            exact (disp_local_iso_cleaving_invertible_2cell h (gg ;; hh) (idempunitor c)).
        + refine (_ •• _).
          * refine (disp_rwhisker _ _).
            exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (ff ;; gg) (idempunitor c))).
          * exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (local_iso_cleaving_1cell h (ff;; gg) (idempunitor c);; hh) (idempunitor c))).
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
        + exact (disp_local_iso_cleaving_invertible_2cell h (f ;; g1) (idempunitor c)).
        + exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (f ;; g2) (idempunitor c))).
      - intros a1 a2 a3 f1 f2 g x.
        assert (linvunitor _ • (id2 _ ▹ identity _) • lunitor _ = id2 (identity c)) as Heq.
        {
          abstract (rewrite id2_rwhisker ;
                    rewrite id2_right ;
                    apply linvunitor_lunitor).
        }
        refine (transportf (λ z, _ ==>[ z ] _) Heq _).
        refine (_ •• (x ▹▹ g) •• _).
        + exact (disp_local_iso_cleaving_invertible_2cell h (f1 ;; g) (idempunitor c)).
        + exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell h (f2 ;; g) (idempunitor c))).
    Defined.

    Local Arguments transportf {_} {_} {_} {_} {_} _.
    Local Arguments transportb {_} {_} {_} {_} {_} _.

    Definition discete_fiber_data_laws_vcomp_left
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

    Definition discete_fiber_data_laws_vcomp_right
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

    Definition discrete_fiber_data_laws_vcomp_assoc
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

    Definition discrete_fiber_data_laws_rwhisker_id2
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
      apply (@transportf_transpose_left _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      refine (disp_vcomp_rinv
                (disp_local_iso_cleaving_invertible_2cell h (f;; g) (idempunitor c))
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
      apply (@transportf_transpose_left _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      refine (disp_vcomp_rinv
                (disp_local_iso_cleaving_invertible_2cell h (f;; g) (idempunitor c))
                @ _).
      unfold transportb.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_vcomp_lwhisker
      :  ∏ (a₁ a₂ a₃ : discrete_fiber_data)
           (f : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (g₁ g₂ g₃ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (x : g₁ ==> g₂)
           (y : g₂ ==> g₃),
         (f ◃ x) • (f ◃ y) = f ◃ (x • y).
    Proof.
      intros a₁ a₂ a₃ f g₁ g₂ g₃ x y ; cbn.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        apply maponpaths.
        apply disp_mor_transportf_postwhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocr _ _ _ @ _).
                apply maponpaths.
                etrans.
                {
                  apply maponpaths_2.
                  exact (disp_vcomp_linv
                           (disp_local_iso_cleaving_invertible_2cell
                              h (f;; g₂)
                              (idempunitor c))).
                }
                etrans.
                {
                  apply disp_mor_transportf_postwhisker.
                }
                etrans.
                {
                  apply maponpaths.
                  apply disp_id2_left.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              etrans.
              {
                apply maponpaths_2.
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                apply disp_lwhisker_vcomp.
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply disp_rwhisker_transport_right.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_postwhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        apply disp_vassocl.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_vcomp_rwhisker
      : ∏ (a₁ a₂ a₃ : discrete_fiber_data)
          (f₁ f₂ f₃ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
          (g : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
          (x : f₁ ==> f₂)
          (y : f₂ ==> f₃),
        (x ▹ g) • (y ▹ g) = (x • y) ▹ g.
    Proof.
      intros a₁ a₂ a₃ f₁ f₂ f₃ f₄ x y ; cbn.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        apply maponpaths.
        apply disp_mor_transportf_prewhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocr _ _ _ @ _).
                apply maponpaths.
                etrans.
                {
                  apply maponpaths_2.
                  exact (disp_vcomp_linv
                           (disp_local_iso_cleaving_invertible_2cell
                              h (f₂;; f₄) (idempunitor c))).
                }
                etrans.
                {
                  apply disp_mor_transportf_postwhisker.
                }
                etrans.
                {
                  apply maponpaths.
                  apply disp_id2_left.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              etrans.
              {
                apply maponpaths_2.
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            refine (disp_vassocl _ _ _ @ _).
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply disp_rwhisker_vcomp.
            }
            apply disp_mor_transportf_prewhisker.
          }
          etrans.
          {
            apply maponpaths_2.
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply disp_rwhisker_transport_left_new.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_postwhisker.
      }
      refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                             _ _ _ _ _ _ @ _).
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_vcomp_lunitor
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
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell
                                  h (id_disp a;; g) (idempunitor c))).
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
      refine (_ @ _).
      {
        apply maponpaths.
        apply disp_vassocr.
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_vcomp_runitor
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
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell
                                  h (g;;id_disp b) (idempunitor c))).
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
      refine (_ @ _).
      {
        apply maponpaths.
        apply disp_vassocr.
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_lwhisker_lwhisker
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
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        etrans.
        {
          apply maponpaths.
          apply disp_mor_transportf_prewhisker.
        }
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              apply disp_rwhisker_transport_right.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_postwhisker.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        apply maponpaths.
        apply disp_mor_transportf_prewhisker.
      }
      refine (!_).
      do 3 (refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                                     _ _ _ _ _ _ @ _)).
      do 2 refine (_ @ !(@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                                          _ _ _ _ _ _)).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (disp_vassocr _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths_2.
                  etrans.
                  {
                    apply maponpaths_2.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        refine (disp_vassocr _ _ _ @ _).
                        etrans.
                        {
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths_2.
                            exact (disp_vcomp_linv
                                     (disp_local_iso_cleaving_invertible_2cell
                                        h
                                        (f₁;; local_iso_cleaving_1cell
                                           h (f₂;; g₂) (idempunitor c))
                                        (idempunitor c))).
                          }
                          etrans.
                          {
                            apply disp_mor_transportf_postwhisker.
                          }
                          etrans.
                          {
                            apply maponpaths.
                            apply disp_id2_left.
                          }
                          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                        }
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      apply disp_mor_transportf_postwhisker.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        etrans.
                        {
                          apply disp_lwhisker_vcomp.
                        }
                        apply maponpaths.
                        etrans.
                        {
                          apply maponpaths.
                          apply disp_vassocl.
                        }
                        etrans.
                        {
                          apply disp_rwhisker_transport_right.
                        }
                        etrans.
                        {
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths.
                            etrans.
                            {
                              apply maponpaths.
                              exact (disp_vcomp_linv
                                       (disp_local_iso_cleaving_invertible_2cell
                                          h (f₂;; g₂) (idempunitor c))).
                            }
                            etrans.
                            {
                              apply disp_mor_transportf_prewhisker.
                            }
                            etrans.
                            {
                              apply maponpaths.
                              apply disp_id2_right.
                            }
                            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                          }
                          apply disp_rwhisker_transport_right.
                        }
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      etrans.
                      {
                        apply maponpaths_2.
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      apply disp_mor_transportf_postwhisker.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths_2.
                apply disp_lwhisker_vcomp_alt.
              }
              etrans.
              {
                apply disp_mor_transportf_postwhisker.
              }
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocl _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    apply disp_lwhisker_lwhisker.
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            refine (disp_vassocl _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocl _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    apply disp_vcomp_whisker_alt.
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocl _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocl _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    refine (disp_vassocl _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths.
                        refine (disp_vassocr _ _ _ @ _).
                        etrans.
                        {
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths_2.
                            refine (disp_vassocr _ _ _ @ _).
                            etrans.
                            {
                              apply maponpaths.
                              etrans.
                              {
                                apply maponpaths_2.
                                exact (disp_vcomp_linv
                                         (disp_local_iso_cleaving_invertible_2cell
                                            h
                                            (local_iso_cleaving_1cell
                                               h (f₁;; f₂) (idempunitor c);; g₁)
                                            (idempunitor c))).
                              }
                              etrans.
                              {
                                apply disp_mor_transportf_postwhisker.
                              }
                              etrans.
                              {
                                apply maponpaths.
                                apply disp_id2_left.
                              }
                              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                            }
                            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                          }
                          apply disp_mor_transportf_postwhisker.
                        }
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      apply disp_mor_transportf_prewhisker.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply disp_mor_transportf_prewhisker.
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                apply disp_vassocr.
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply disp_vassocr.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        etrans.
        {
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply disp_vassocr.
        }
        apply disp_mor_transportf_prewhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply cellset_property.
    Qed.

    Definition discrete_fiber_data_laws_rwhisker_lwhisker
      : ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data)
          (f₁ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
          (f₂ f₃ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
          (f₄ : discrete_fiber_data ⟦ a₃ , a₄ ⟧)
          (x : f₂ ==> f₃),
        (f₁ ◃ (x ▹ f₄)) • lassociator f₁ f₃ f₄
        =
        lassociator f₁ f₂ f₄ • ((f₁ ◃ x) ▹ f₄).
    Proof.
      intros a₁ a₂ a₃ a₄ f₁ f₂ f₃ f₄ x ; cbn.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              apply disp_rwhisker_transport_right.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_postwhisker.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        apply maponpaths.
        apply disp_mor_transportf_prewhisker.
      }
      refine (!_).
      do 3 (refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                                     _ _ _ _ _ _ @ _)).
      do 2 refine (_ @ !(@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                                        _ _ _ _ _ _)).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (disp_vassocl _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        exact (disp_vcomp_linv
                                 (disp_local_iso_cleaving_invertible_2cell
                                    h
                                    (f₁;; local_iso_cleaving_1cell
                                       h (f₃;; f₄) (idempunitor c))
                                    (idempunitor c))).
                      }
                      etrans.
                      {
                        apply disp_mor_transportf_postwhisker.
                      }
                      etrans.
                      {
                        apply maponpaths.
                        apply disp_id2_left.
                      }
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (disp_vassocr _ _ _ @ _).
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths_2.
                  refine (disp_vassocr _ _ _ @ _).
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      refine (disp_lwhisker_vcomp _ _ @ _).
                      etrans.
                      {
                        apply maponpaths.
                        etrans.
                        {
                          apply maponpaths.
                          refine (disp_vassocl _ _ _ @ _).
                          etrans.
                          {
                            apply maponpaths.
                            etrans.
                            {
                              apply maponpaths.
                              exact (disp_vcomp_linv
                                       (disp_local_iso_cleaving_invertible_2cell
                                          h (f₃;; f₄) (idempunitor c))).
                            }
                            apply disp_mor_transportf_prewhisker.
                          }
                          etrans.
                          {
                            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                          }
                          etrans.
                          {
                            apply maponpaths.
                            apply disp_id2_right.
                          }
                          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                        }
                        apply disp_rwhisker_transport_right.
                      }
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    apply disp_mor_transportf_postwhisker.
                  }
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply disp_mor_transportf_postwhisker.
            }
            etrans.
            {
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }


      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths_2.
                apply disp_lwhisker_vcomp_alt.
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              refine (disp_vassocl _ _ _ @ _).
              do 2 apply maponpaths.
              apply disp_rwhisker_lwhisker.
            }
            unfold transportb.
            apply disp_mor_transportf_postwhisker.
          }
          etrans.
          {
            apply disp_mor_transportf_postwhisker.
          }
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply disp_mor_transportf_prewhisker.
        }
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              apply disp_rwhisker_transport_left_new.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                             _ _ _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            refine (disp_vassocl _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocl _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        exact (disp_vcomp_linv
                                 (disp_local_iso_cleaving_invertible_2cell
                                    h
                                    (local_iso_cleaving_1cell
                                       h (f₁;; f₂) (idempunitor c);; f₄) (idempunitor c))).
                      }
                      etrans.
                      {
                        apply disp_mor_transportf_postwhisker.
                      }
                      etrans.
                      {
                        apply maponpaths.
                        apply disp_id2_left.
                      }
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocl _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocl _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      apply disp_rwhisker_vcomp.
                    }
                    etrans.
                    {
                      apply disp_mor_transportf_postwhisker.
                    }
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      etrans.
                      {
                        apply maponpaths.
                        refine (disp_vassocr _ _ _ @ _).
                        etrans.
                        {
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths_2.
                            refine (disp_vassocr _ _ _ @ _).
                            etrans.
                            {
                              apply maponpaths.
                              etrans.
                              {
                                apply maponpaths_2.
                                exact (disp_vcomp_linv
                                         (disp_local_iso_cleaving_invertible_2cell
                                            h (f₁;; f₂) (idempunitor c))).
                              }
                              etrans.
                              {
                                apply disp_mor_transportf_postwhisker.
                              }
                              etrans.
                              {
                                apply maponpaths.
                                apply disp_id2_left.
                              }
                              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                            }
                            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                          }
                          apply disp_mor_transportf_postwhisker.
                        }
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      etrans.
                      {
                        apply disp_rwhisker_transport_left_new.
                      }
                      etrans.
                      {
                        apply maponpaths.
                        apply disp_rwhisker_vcomp_alt.
                      }
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    apply disp_mor_transportf_postwhisker.
                  }
                  etrans.
                  {
                    apply maponpaths.
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply disp_mor_transportf_prewhisker.
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocl _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocl _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocl _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    apply disp_vassocr.
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply cellset_property.
    Qed.

    Definition discrete_fiber_data_laws_rwhisker_rwhisker
      :  ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data)
           (f₁ f₂ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (f₃ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (f₄ : discrete_fiber_data ⟦ a₃ , a₄ ⟧)
           (x : f₁ ==> f₂),
         lassociator f₁ f₃ f₄ • ((x ▹ f₃) ▹ f₄)
         =
         (x ▹ f₃ · f₄) • lassociator f₂ f₃ f₄.
    Proof.
      intros a₁ a₂ a₃ a₄ f₁ f₂ f₃ f₄ x ; cbn.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              apply disp_rwhisker_transport_left_new.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      do 3 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_postwhisker.
        }
        apply maponpaths.
        apply disp_mor_transportf_prewhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (disp_vassocr _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths_2.
                  refine (disp_vassocr _ _ _ @ _).
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      exact (disp_vcomp_linv
                               (disp_local_iso_cleaving_invertible_2cell
                                  h
                                  (f₂;; local_iso_cleaving_1cell h (f₃;; f₄) (idempunitor c))
                                  (idempunitor c))).
                    }
                    apply disp_mor_transportf_postwhisker.
                  }
                  etrans.
                  {
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply maponpaths.
                  apply disp_id2_left.
                }
                etrans.
                {
                  apply disp_mor_transportf_postwhisker.
                }
                etrans.
                {
                  apply maponpaths.
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply disp_mor_transportf_prewhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (disp_vassocl _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              refine (disp_vassocr _ _ _ @ _).
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocl _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        apply (disp_vcomp_linv
                                 (disp_local_iso_cleaving_invertible_2cell
                                    h
                                    (local_iso_cleaving_1cell h (f₁;; f₃) (idempunitor c);; f₄)
                                    (idempunitor c))).
                      }
                      apply disp_mor_transportf_postwhisker.
                    }
                    etrans.
                    {
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    etrans.
                    {
                      apply maponpaths.
                      apply disp_id2_left.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_prewhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                apply disp_rwhisker_vcomp.
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        apply (disp_vcomp_linv
                                 (disp_local_iso_cleaving_invertible_2cell
                                    h (f₁;; f₃)
                                    (idempunitor c))).
                      }
                      etrans.
                      {
                        apply disp_mor_transportf_postwhisker.
                      }
                      apply maponpaths.
                      apply disp_id2_left.
                    }
                    etrans.
                    {
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_rwhisker_transport_left_new.
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply disp_rwhisker_vcomp_alt.
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (disp_vassocr _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths_2.
                  apply disp_rwhisker_rwhisker.
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        apply disp_vcomp_whisker_alt.
                      }
                      apply disp_mor_transportf_postwhisker.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (disp_vassocr _ _ _ @ _).
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths_2.
                  apply disp_vassocr.
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply disp_mor_transportf_postwhisker.
            }
            etrans.
            {
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply cellset_property.
    Qed.

    Definition discrete_fiber_data_vcomp_whisker
      :  ∏ (a₁ a₂ a₃ : discrete_fiber_data)
           (f₁ f₂ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (g₁ g₂ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (x : f₁ ==> f₂) (y : g₁ ==> g₂),
         (x ▹ g₁) • (f₂ ◃ y) = (f₁ ◃ y) • (x ▹ g₂).
    Proof.
      intros a₁ a₂ a₃ f₁ f₂ g₁ g₂ x y ; cbn.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        etrans.
        {
          apply maponpaths.
          apply disp_mor_transportf_postwhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        etrans.
        {
          apply maponpaths.
          apply disp_mor_transportf_postwhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              refine (disp_vassocl _ _ _ @ _).
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    exact (disp_vcomp_linv
                             (disp_local_iso_cleaving_invertible_2cell
                                h (f₁;; g₂) (idempunitor c))).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    apply disp_id2_left.
                  }
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_postwhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (disp_vassocl _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    exact (disp_vcomp_linv
                             (disp_local_iso_cleaving_invertible_2cell
                                h (f₂;; g₁) (idempunitor c))).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    apply disp_id2_left.
                  }
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                apply disp_vcomp_whisker.
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocl _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply disp_vassocr.
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply cellset_property.
    Qed.

    Definition discrete_fiber_data_laws_lunitor_linvunitor
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
        apply (disp_vcomp_rinv (disp_local_iso_cleaving_invertible_2cell h (id_disp a;; f) (idempunitor c))).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_linvunitor_lunitor
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
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (id_disp a;; f) (idempunitor c))).
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

    Definition discrete_fiber_data_laws_runitor_rinvunitor
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
                                                           (idempunitor c))).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.

    Definition discrete_fiber_data_laws_rinvunitor_runitor
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
        apply (disp_vcomp_linv (disp_local_iso_cleaving_invertible_2cell h (f ;; id_disp b) (idempunitor c))).
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

    Definition discrete_fiber_data_laws_lassociator_rassociator
      :  ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data)
           (f₁ : discrete_fiber_data ⟦ a₁ , a₂ ⟧)
           (f₂ : discrete_fiber_data ⟦ a₂ , a₃ ⟧)
           (f₃ : discrete_fiber_data ⟦ a₃ , a₄ ⟧),
         lassociator f₁ f₂ f₃ • rassociator f₁ f₂ f₃
         =
         id₂ (f₁ · (f₂ · f₃)).
    Proof.
      intros a₁ a₂ a₃ a₄ f₁ f₂ f₃ ; cbn.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply disp_mor_transportf_prewhisker.
        }
        apply maponpaths.
        apply disp_mor_transportf_postwhisker.
      }
      do 2 refine (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)
                                  _ _ _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocl _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (disp_vassocr _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths_2.
                    refine (disp_vassocr _ _ _ @ _).
                    etrans.
                    {
                      apply maponpaths.
                      etrans.
                      {
                        apply maponpaths_2.
                        refine (disp_vassocr _ _ _ @ _).
                        etrans.
                        {
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths_2.
                            exact (disp_vcomp_linv
                                     (disp_local_iso_cleaving_invertible_2cell
                                        h
                                        (local_iso_cleaving_1cell
                                           h (f₁;; f₂) (idempunitor c);; f₃)
                                        (idempunitor c))).
                          }
                          apply disp_mor_transportf_postwhisker.
                        }
                        etrans.
                        {
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths.
                            apply disp_id2_left.
                          }
                          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                        }
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      apply disp_mor_transportf_postwhisker.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (disp_vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              refine (disp_vassocr _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths_2.
                  refine (disp_vassocr _ _ _ @ _).
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      refine (disp_rwhisker_vcomp _ _ @ _).
                      etrans.
                      {
                        apply maponpaths.
                        etrans.
                        {
                          apply maponpaths.
                          exact (disp_vcomp_linv
                                   (disp_local_iso_cleaving_invertible_2cell
                                      h (f₁;; f₂) (idempunitor c))).
                        }
                        apply disp_rwhisker_transport_left_new.
                      }
                      etrans.
                      {
                        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                      }
                      etrans.
                      {
                        apply maponpaths.
                        apply disp_id2_rwhisker.
                      }
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    etrans.
                    {
                      apply disp_mor_transportf_postwhisker.
                    }
                    etrans.
                    {
                      apply maponpaths.
                      apply disp_id2_left.
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply disp_lassociator_rassociator.
            }
            apply disp_mor_transportf_postwhisker.
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply disp_id2_left.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (disp_vassocl _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                apply disp_lwhisker_vcomp.
              }
              apply disp_mor_transportf_postwhisker.
            }
            etrans.
            {
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  exact (disp_vcomp_rinv
                           (disp_local_iso_cleaving_invertible_2cell
                              h (f₂;; f₃) (idempunitor c))).
                }
                etrans.
                {
                  apply disp_rwhisker_transport_right.
                }
                etrans.
                {
                  apply maponpaths.
                  apply disp_lwhisker_id2.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                apply disp_id2_left.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      etrans.
      {
        apply maponpaths.
        exact (disp_vcomp_rinv
                 (disp_local_iso_cleaving_invertible_2cell
                    h
                    (f₁;; local_iso_cleaving_1cell h (f₂;; f₃) (idempunitor c))
                    (idempunitor c))).
      }
      etrans.
      {
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
      apply C.
    Qed.
  End Discrete_Fiber.
End LocalIsoFibration.
