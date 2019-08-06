(* ******************************************************************************* *)
(** * Fiber category of a displayed bicategory whose displayed 2-cells form a
      proposition. In addition, we ask the displayed bicategory to be locally univalent and
      to be equipped with a local iso-cleaving.
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
    Variable (D : disp_bicat C)
             (HD : disp_2cells_isaprop D)
             (HD_2_1 : disp_univalent_2_1 D)
             (h : local_iso_cleaving D)
             (c : C).

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

    (** Laws of category *)

    (** Left unitality *)
    Definition discrete_fiber_lunitor
               {d d' : D c}
               (ff : d -->[ id₁ c] d')
      : (local_iso_cleaving_1cell h (id_disp d;; ff) idempunitor)
          ==>[ id₂ (id₁ c)] ff.
    Proof.
      set (PP := disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) idempunitor).
      set (RR := PP •• disp_lunitor ff).
      assert (Heq : idempunitor • lunitor (identity c) = id2 (identity c)).
      { abstract (apply linvunitor_lunitor). }
      exact (transportf (λ x, _ ==>[x] _) Heq RR).
    Defined.

    Definition discrete_fiber_linvunitor
               {d d' : D c}
               (ff : d -->[ id₁ c] d')
      : ff ==>[id₂ (id₁ c) ]
           (local_iso_cleaving_1cell h (id_disp d;; ff) idempunitor).
    Proof.
      set (PP := disp_inv_cell
                   (disp_local_iso_cleaving_invertible_2cell
                      h
                      (id_disp d;; ff) idempunitor)).
      assert (Heq : linvunitor (identity c) • idempunitor^-1 = id2 (identity c)).
      { abstract (apply linvunitor_lunitor). }
      exact (transportf (λ x, _ ==>[x] _) Heq (disp_linvunitor ff •• PP)).
    Defined.

    Definition discrete_fiber_lunitor_disp_invertible
               {d d' : D c}
               (ff : d -->[ id₁ c] d')
      : disp_invertible_2cell
          (id2_invertible_2cell (id₁ c))
          (local_iso_cleaving_1cell h (id_disp d;; ff) idempunitor)
          ff.
    Proof.
      use tpair.
      - exact (discrete_fiber_lunitor ff).
      - use tpair.
        + exact (discrete_fiber_linvunitor ff).
        + abstract (split ; apply HD).
    Defined.

    (** Right unitality *)
    Definition discrete_fiber_runitor
               {d d' : D c}
               (ff : d -->[ id₁ c] d')
      : (local_iso_cleaving_1cell h (ff;;id_disp d') idempunitor)
          ==>[ id₂ (id₁ c)] ff.
    Proof.
      assert (Heq : idempunitor • runitor (identity c) = id2 (identity c)).
      { abstract (cbn
                  ; rewrite <- lunitor_runitor_identity, linvunitor_lunitor
                  ; reflexivity).
      }
      set (PP := disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') idempunitor).
      exact (transportf (λ x, _ ==>[x] _) Heq (PP •• disp_runitor ff)).
    Defined.

    Definition discrete_fiber_rinvunitor
               {d d' : D c}
               (ff : d -->[ id₁ c] d')
      : ff ==>[ id₂ (id₁ c) ]
           (local_iso_cleaving_1cell h (ff;;id_disp d') idempunitor).
    Proof.
      set (PP := disp_inv_cell
                   (disp_local_iso_cleaving_invertible_2cell
                      h (ff;; id_disp d') idempunitor)).
      assert (Heq : rinvunitor (identity c) • idempunitor^-1 = id2 (identity c)).
      { unfold idempunitor. cbn.
        abstract (rewrite lunitor_runitor_identity, rinvunitor_runitor
                  ; reflexivity).
      }
      exact (transportf (λ x, _ ==>[x] _) Heq (disp_rinvunitor ff •• PP)).
    Defined.

    Definition discrete_fiber_runitor_disp_invertible
               {d d' : D c}
               (ff : d -->[ id₁ c] d')
      : disp_invertible_2cell
          (id2_invertible_2cell (id₁ c))
          (local_iso_cleaving_1cell h (ff;;id_disp d') idempunitor)
          ff.
    Proof.
      use tpair.
      - exact (discrete_fiber_runitor ff).
      - use tpair.
        + exact (discrete_fiber_rinvunitor ff).
        + abstract (split ; apply HD).
    Defined.

    (** Associativity *)
    Definition discrete_fiber_lassociator
               {d0 d1 d2 d3 : D c}
               (ff : d0 -->[ id₁ c] d1)
               (gg : d1 -->[ id₁ c] d2)
               (hh : d2 -->[ id₁ c] d3)
      : local_iso_cleaving_1cell
          h
          (ff;; local_iso_cleaving_1cell h (gg;; hh) idempunitor)
          idempunitor
        ==>[ id₂ (id₁ c)]
        local_iso_cleaving_1cell h
          (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh)
          idempunitor.
    Proof.
      assert ((idempunitor
                 • (identity c ◃ idempunitor))
                • lassociator _ _ _
                • ((lunitor _ ▹ identity c)
                     • lunitor _) = id2 _) as Heq.
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
        - refine (_ •• _).
          + exact (disp_local_iso_cleaving_invertible_2cell
                     h (ff;;local_iso_cleaving_1cell h (gg;; hh) idempunitor)
                     idempunitor).
          + refine (disp_lwhisker _ _).
            exact (disp_local_iso_cleaving_invertible_2cell
                     h (gg ;; hh) idempunitor).
        - refine (_ •• _).
          + refine (disp_rwhisker _ _).
            exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell
                                    h (ff ;; gg) idempunitor)).
          + exact (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell
                                    h (local_iso_cleaving_1cell h (ff;; gg) idempunitor;;
                                                                hh) idempunitor)).
    Defined.

    Definition discrete_fiber_rassociator
               {d0 d1 d2 d3 : D c}
               (ff : d0 -->[ id₁ c] d1)
               (gg : d1 -->[ id₁ c] d2)
               (hh : d2 -->[ id₁ c] d3)
      : local_iso_cleaving_1cell
           h (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh)
           idempunitor
        ==>[ id₂ (id₁ c)]
        local_iso_cleaving_1cell
          h
          (ff;; local_iso_cleaving_1cell h (gg;; hh) idempunitor) idempunitor.
    Proof.
      assert ((idempunitor • (idempunitor ▹ identity c))
                • rassociator _ _ _
                • ((identity c ◃ lunitor _)
                     • lunitor _)
              = id2 _) as Heq.
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
      - refine (disp_local_iso_cleaving_invertible_2cell
                  h (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh) idempunitor
                  •• _).
        refine (disp_rwhisker _ _).
        exact (disp_local_iso_cleaving_invertible_2cell h (ff ;; gg) idempunitor).
      - refine (_ •• _).
        + refine (disp_lwhisker _ _).
          exact (disp_inv_cell
                   (disp_local_iso_cleaving_invertible_2cell
                      h (gg ;; hh) idempunitor)).
        + exact (disp_inv_cell ((disp_local_iso_cleaving_invertible_2cell
                                   h
                                   (ff;;local_iso_cleaving_1cell
                                      h (gg;; hh)
                                      idempunitor)
                                   idempunitor))).
    Defined.

    Definition discrete_fiber_lassociator_disp_invertible
               {d0 d1 d2 d3 : D c}
               (ff : d0 -->[ id₁ c] d1)
               (gg : d1 -->[ id₁ c] d2)
               (hh : d2 -->[ id₁ c] d3)
      : disp_invertible_2cell
          (id2_invertible_2cell (id₁ c))
          (local_iso_cleaving_1cell
             h
             (ff;; local_iso_cleaving_1cell h (gg;; hh) idempunitor)
             idempunitor)
          (local_iso_cleaving_1cell
             h
             (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh)
             idempunitor).
    Proof.
      use tpair.
      - exact (discrete_fiber_lassociator ff gg hh).
      - use tpair.
        + exact (discrete_fiber_rassociator ff gg hh).
        + abstract (split ; apply HD).
    Defined.

    (** Now let's assemble it! *)
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

    Definition discrete_fiber_is_precategory
      : is_precategory discrete_fiber_precategory_data.
    Proof.
      apply is_precategory_one_assoc_to_two.
      repeat split.
      - cbn ; intros a b f.
        exact (disp_isotoid_2_1
                 D HD_2_1
                 (idpath _)
                 _
                 _
                 (discrete_fiber_lunitor_disp_invertible f)).
      - cbn ; intros a b f.
        exact (disp_isotoid_2_1
                 D HD_2_1
                 (idpath _)
                 _
                 _
                 (discrete_fiber_runitor_disp_invertible f)).
      -intros d0 d1 d2 d3 ff gg hh.
        exact (disp_isotoid_2_1
                 D HD_2_1
                 (idpath _)
                 _
                 _
                 (discrete_fiber_lassociator_disp_invertible ff gg hh)).
    Qed.

    Definition discrete_fiber_precategory : precategory.
    Proof.
      use make_precategory.
      - exact discrete_fiber_precategory_data.
      - exact discrete_fiber_is_precategory.
    Defined.

    Definition discrete_fiber_category : category.
    Proof.
      use make_category.
      - exact discrete_fiber_precategory.
      - intros x y f g.
        apply (isofhlevelweqb 1 (make_weq _ (HD_2_1 _ _ _ _ (idpath _) x y f g))).
        use isofhleveltotal2.
        + apply HD.
        + intros.
          apply isaprop_is_disp_invertible_2cell.
    Defined.
  End Discrete_Fiber.
End LocalIsoFibration.

Definition univalent_2_1_to_local_iso_cleaving_help
           {C : bicat}
           {D : disp_prebicat C}
           {c c' : C}
           {f f' : C⟦c,c'⟧}
           {d : D c} {d' : D c'}
           (ff' : d -->[f'] d')
           (α : f  = f')
  : ∑ ff : d -->[f] d', disp_invertible_2cell (idtoiso_2_1 _ _ α) ff ff'.
Proof.
  induction α.
  refine (ff' ,, _).
  apply disp_id2_invertible_2cell.
Defined.

Definition univalent_2_1_to_local_iso_cleaving
           {C : bicat}
           (HC : is_univalent_2_1 C)
           (D : disp_prebicat C)
  : local_iso_cleaving D.
Proof.
  intros x y f g xx yy ff gg.
  pose (univalent_2_1_to_local_iso_cleaving_help ff (isotoid_2_1 HC gg)) as t.
  rewrite idtoiso_2_1_isotoid_2_1 in t.
  exact t.
Defined.
