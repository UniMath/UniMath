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
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Fibration.Fibration1.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section LocalIsoFibration.
  Context {C : bicat}.

  Variable (D : disp_prebicat C) (h : local_iso_cleaving D) (c : C).

  Local Arguments transportf {_} {_} {_} {_} {_} _.
  Local Arguments transportb {_} {_} {_} {_} {_} _.

  Definition discrete_fiber_data_laws_rassociator_lassociator
    :  ∏ (a₁ a₂ a₃ a₄ : discrete_fiber_data D h c)
         (f₁ : discrete_fiber_data D h c ⟦ a₁ , a₂ ⟧)
         (f₂ : discrete_fiber_data D h c ⟦ a₂ , a₃ ⟧)
         (f₃ : discrete_fiber_data D h c ⟦ a₃ , a₄ ⟧),
       rassociator f₁ f₂ f₃ • lassociator f₁ f₂ f₃
       =
       id₂ (f₁ · f₂ · f₃).
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
      etrans.
      {
        refine (disp_vassocl _ _ _ @ _).
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
                                    h
                                    (f₁;; local_iso_cleaving_1cell
                                       h (f₂;; f₃) (idempunitor c))
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
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                apply disp_lwhisker_vcomp.
              }
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    exact (disp_vcomp_linv
                             (disp_local_iso_cleaving_invertible_2cell
                                h (f₂;; f₃) (idempunitor c))).
                  }
                  apply disp_rwhisker_transport_right.
                }
                etrans.
                {
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                etrans.
                {
                  apply maponpaths.
                  apply disp_lwhisker_id2.
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
              apply disp_rassociator_lassociator.
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
              etrans.
              {
                apply disp_rwhisker_vcomp.
              }
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                exact (disp_vcomp_rinv
                         (disp_local_iso_cleaving_invertible_2cell
                            h (f₁;; f₂) (idempunitor c))).
              }
              etrans.
              {
                apply disp_rwhisker_transport_left_new.
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
              apply maponpaths_2.
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
                  (local_iso_cleaving_1cell
                     h (f₁;; f₂) (idempunitor c);; f₃)
                  (idempunitor c))).
    }
    etrans.
    {
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    }
    apply (transportf_set (λ α : id₁ c ==> id₁ c, _ ==>[ α] _) _).
    apply C.
  Qed.

  Definition discrete_fiber_data_laws_runitor_rwhisker
    : ∏ (a₁ a₂ a₃ : discrete_fiber_data D h c)
        (f : discrete_fiber_data D h c ⟦ a₁ , a₂ ⟧)
        (g : discrete_fiber_data D h c ⟦ a₂ , a₃ ⟧),
      lassociator f (id₁ a₂) g • (runitor f ▹ g)
      =
      f ◃ lunitor g.
  Proof.
    intros a₁ a₂ a₃ f g ; cbn.
    etrans.
    {
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
      etrans.
      {
        apply disp_mor_transportf_prewhisker.
      }
      apply maponpaths.
      apply disp_mor_transportf_postwhisker.
    }
    do 3 refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                                _ _ _ _ _ _ @ _).
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
    refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                           _ _ _ _ _ _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (disp_vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      refine (disp_vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      refine (disp_vassocr _ _ _ @ _).
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
                        (local_iso_cleaving_1cell h (f;; id_disp a₂) (idempunitor c);; g)
                        (idempunitor c))).
          }
          unfold transportb.
          etrans.
          {
            apply disp_mor_transportf_postwhisker.
          }
          etrans.
          {
            apply maponpaths.
            exact (disp_id2_left _).
          }
          unfold transportb.
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        unfold transportb.
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
      apply disp_mor_transportf_postwhisker.
    }
    unfold transportb.
    refine (@transport_f_f _ (λ z : id₁ c ==> id₁ c, _ ==>[ z ] _)
                           _ _ _ _ _ _ @ _).
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
            etrans.
            {
              apply maponpaths.
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
            etrans.
            {
              apply disp_rwhisker_vcomp.
            }
            etrans.
            {
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
                    exact (disp_vcomp_linv
                             (disp_local_iso_cleaving_invertible_2cell
                                h
                                (f;; id_disp a₂) (idempunitor c))).
                  }
                  etrans.
                  {
                    apply disp_mor_transportf_postwhisker.
                  }
                  apply maponpaths.
                  apply disp_id2_left.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              etrans.
              {
                apply maponpaths.
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_rwhisker_transport_left_new.
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
              apply disp_runitor_rwhisker.
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
      exact (disp_vassocl _ _ _).
    }
    etrans.
    {
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    }
    apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
    apply cellset_property.
  Qed.

  Definition discrete_fiber_data_laws_lassociator_lassociator
    : ∏ (a₁ a₂ a₃ a₄ a₅ : discrete_fiber_data D h c)
        (f₁ : discrete_fiber_data D h c ⟦ a₁ , a₂ ⟧)
        (f₂ : discrete_fiber_data D h c ⟦ a₂ , a₃ ⟧)
        (f₃ : discrete_fiber_data D h c ⟦ a₃ , a₄ ⟧)
        (f₄ : discrete_fiber_data D h c ⟦ a₄ , a₅ ⟧),
      ((f₁ ◃ lassociator f₂ f₃ f₄)
         • lassociator f₁ (f₂ · f₃) f₄)
        • (lassociator f₁ f₂ f₃ ▹ f₄)
      =
      lassociator f₁ f₂ (f₃ · f₄) • lassociator (f₁ · f₂) f₃ f₄.
  Proof.
    intros a₁ a₂ a₃ a₄ a₅ f₁ f₂ f₃ f₄ ; cbn.
    etrans.
    {
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
          etrans.
          {
            apply disp_mor_transportf_postwhisker.
          }
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply disp_mor_transportf_prewhisker.
          }
          etrans.
          {
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
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
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
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
          apply disp_mor_transportf_postwhisker.
        }
        etrans.
        {
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        etrans.
        {
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
        }
        etrans.
        {
          apply maponpaths.
          apply disp_mor_transportf_prewhisker.
        }
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
      }
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
            refine (disp_vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              etrans.
              {apply maponpaths_2.
               refine (disp_vassocr _ _ _ @ _).
               etrans.
               {
                 apply maponpaths.
                 etrans.
                 {
                   apply maponpaths_2.
                   etrans.
                   {
                     refine (disp_vassocr _ _ _ @ _).
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
                                       (f₁;;local_iso_cleaving_1cell h
                                          (local_iso_cleaving_1cell
                                             h (f₂;; f₃) (idempunitor c);; f₄)
                                          (idempunitor c))
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
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                                       h (f₁;; local_iso_cleaving_1cell h (f₂;; f₃) (idempunitor c))
                                       (idempunitor c);; f₄)
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
              etrans.
              {
                apply disp_rwhisker_vcomp.
              }
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
                                        (f₁;;local_iso_cleaving_1cell
                                           h (f₂;; f₃) (idempunitor c))
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
              apply disp_rwhisker_transport_left_new.
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
        apply maponpaths_2.
        etrans.
        {
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
              apply disp_vassocl.
            }
            etrans.
            {
              apply disp_rwhisker_transport_right.
            }
            apply maponpaths.
            apply disp_lwhisker_vcomp_alt.
          }
          etrans.
          {
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                      apply disp_lwhisker_vcomp.
                    }
                    etrans.
                    {
                      apply disp_mor_transportf_postwhisker.
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
                                  refine (disp_vassocl _ _ _ @ _).
                                  etrans.
                                  {
                                    apply maponpaths.
                                    etrans.
                                    {
                                      apply maponpaths.
                                      exact (disp_vcomp_linv
                                               (disp_local_iso_cleaving_invertible_2cell
                                                  h
                                                  (local_iso_cleaving_1cell
                                                     h (f₂;; f₃) (idempunitor c);; f₄)
                                                  (idempunitor c))).
                                    }
                                    etrans.
                                    {
                                      apply disp_mor_transportf_prewhisker.
                                    }
                                    apply maponpaths.
                                    apply disp_id2_right.
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
                            apply disp_mor_transportf_prewhisker.
                          }
                          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                        }
                        apply disp_rwhisker_transport_right.
                      }
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
                apply disp_vassocr.
              }
              etrans.
              {
                apply disp_rwhisker_transport_right.
              }
              etrans.
              {
                apply maponpaths.
                apply disp_lwhisker_vcomp_alt.
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
              refine (disp_vassocl _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  apply disp_rwhisker_lwhisker.
                }
                apply disp_mor_transportf_prewhisker.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                      etrans.
                      {
                        apply disp_rwhisker_vcomp.
                      }
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
                                etrans.
                                {
                                  apply disp_lwhisker_vcomp.
                                }
                                apply maponpaths.
                                etrans.
                                {
                                  apply maponpaths.
                                  exact (disp_vcomp_linv
                                           (disp_local_iso_cleaving_invertible_2cell
                                              h (f₂;; f₃) (idempunitor c))).
                                }
                                etrans.
                                {
                                  apply disp_rwhisker_transport_right.
                                }
                                apply maponpaths.
                                apply disp_lwhisker_id2.
                              }
                              etrans.
                              {
                                apply maponpaths_2.
                                etrans.
                                {
                                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                      apply disp_rwhisker_transport_left_new.
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
            apply disp_mor_transportf_prewhisker.
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                  refine (disp_vassocr _ _ _ @ _).
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      apply (disp_lassociator_lassociator).
                    }
                    apply disp_mor_transportf_postwhisker.
                  }
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      etrans.
      {
        apply maponpaths.
        apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                                         h (f₁;; f₂) (idempunitor c);;
                                         local_iso_cleaving_1cell
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
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
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
                    apply disp_lwhisker_lwhisker.
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
              }
              apply disp_mor_transportf_postwhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
          }
          etrans.
          {
            apply maponpaths.
            apply disp_mor_transportf_postwhisker.
          }
          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
                  apply disp_rwhisker_vcomp_alt.
                }
                etrans.
                {
                  apply disp_mor_transportf_prewhisker.
                }
                apply maponpaths.
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
              etrans.
              {
                apply maponpaths.
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
              apply disp_mor_transportf_prewhisker.
            }
            apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
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
          refine (disp_vassocl _ _ _ @ _).
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
                  apply maponpaths.
                  apply disp_vassocl.
                }
                apply disp_mor_transportf_prewhisker.
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
                refine (disp_vassocl _ _ _ @ _).
                etrans.
                {
                  apply maponpaths.
                  apply disp_vassocl.
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
      apply disp_mor_transportf_prewhisker.
    }
    etrans.
    {
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    }
    apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
    apply cellset_property.
  Qed.

  Definition discrete_fiber_data_laws : prebicat_laws (discrete_fiber_data D h c).
  Proof.
    repeat split.
    - exact (discete_fiber_data_laws_vcomp_left D h c).
    - exact (discete_fiber_data_laws_vcomp_right D h c).
    - exact (discrete_fiber_data_laws_vcomp_assoc D h c).
    - exact (discrete_fiber_data_laws_rwhisker_id2 D h c).
    - exact (discrete_fiber_data_laws_id2_lwhisker D h c).
    - exact (discrete_fiber_data_laws_vcomp_lwhisker D h c).
    - exact (discrete_fiber_data_laws_vcomp_rwhisker D h c).
    - exact (discrete_fiber_data_laws_vcomp_lunitor D h c).
    - exact (discrete_fiber_data_laws_vcomp_runitor D h c).
    - exact (discrete_fiber_data_laws_lwhisker_lwhisker D h c).
    - exact (discrete_fiber_data_laws_rwhisker_lwhisker D h c).
    - exact (discrete_fiber_data_laws_rwhisker_rwhisker D h c).
    - exact (discrete_fiber_data_vcomp_whisker D h c).
    - exact (discrete_fiber_data_laws_lunitor_linvunitor D h c).
    - exact (discrete_fiber_data_laws_linvunitor_lunitor D h c).
    - exact (discrete_fiber_data_laws_runitor_rinvunitor D h c).
    - exact (discrete_fiber_data_laws_rinvunitor_runitor D h c).
    - exact (discrete_fiber_data_laws_lassociator_rassociator D h c).
    - exact discrete_fiber_data_laws_rassociator_lassociator.
    - exact discrete_fiber_data_laws_runitor_rwhisker.
    - exact discrete_fiber_data_laws_lassociator_lassociator.
  Qed.

  Definition discrete_fiber : prebicat.
  Proof.
    use tpair.
    - exact discrete_fiber_data.
    - exact discrete_fiber_data_laws.
  Defined.
End LocalIsoFibration.
