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
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.FiberBicategory1.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section LocalIsoFibration.
  Context {C : bicat}.

  Variable (D : disp_bicat C) (h : local_iso_cleaving D) (c : C).

  Local Arguments transportf {_} {_} {_} {_} {_} _.
  Local Arguments transportb {_} {_} {_} {_} {_} _.
  Local Arguments disp_lassociator {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
  Local Arguments disp_rassociator {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
  Local Notation "'ℓ1'" := (local_iso_cleaving_1cell h _ (idempunitor c))
                             (at level 0).
  Local Notation "'ℓ2'" := (disp_local_iso_cleaving_invertible_2cell h _ (idempunitor c))
                             (at level 0).
  Local Notation "f ^-1" := (disp_inv_cell f).

  Definition strict_fiber_bicat_data_laws_rassociator_lassociator
    :  ∏ (a₁ a₂ a₃ a₄ : strict_fiber_bicat_data D h c)
         (f₁ : strict_fiber_bicat_data D h c ⟦ a₁ , a₂ ⟧)
         (f₂ : strict_fiber_bicat_data D h c ⟦ a₂ , a₃ ⟧)
         (f₃ : strict_fiber_bicat_data D h c ⟦ a₃ , a₄ ⟧),
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

  Definition strict_fiber_bicat_data_laws_runitor_rwhisker
    : ∏ (a₁ a₂ a₃ : strict_fiber_bicat_data D h c)
        (f : strict_fiber_bicat_data D h c ⟦ a₁ , a₂ ⟧)
        (g : strict_fiber_bicat_data D h c ⟦ a₂ , a₃ ⟧),
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

  Section LassociatorLassociator.
    Variable (a₁ a₂ a₃ a₄ a₅ : strict_fiber_bicat_data D h c)
             (f₁ : strict_fiber_bicat_data D h c ⟦ a₁ , a₂ ⟧)
             (f₂ : strict_fiber_bicat_data D h c ⟦ a₂ , a₃ ⟧)
             (f₃ : strict_fiber_bicat_data D h c ⟦ a₃ , a₄ ⟧)
             (f₄ : strict_fiber_bicat_data D h c ⟦ a₄ , a₅ ⟧).
    Arguments transportf {_} _ {_} {_} _ _.

    Local Definition step1
      : ∑ p,
        ((f₁ ◃ lassociator f₂ f₃ f₄)
           • lassociator f₁ (f₂ · f₃) f₄)
          • (lassociator f₁ f₂ f₃ ▹ f₄)
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          ((((ℓ2 •• (f₁ ◃◃ (((ℓ2 •• (f₂ ◃◃ ℓ2)) •• disp_lassociator)
                              •• ((ℓ2 ^-1 ▹▹ f₄) •• ℓ2 ^-1)))) •• ℓ2 ^-1)
              •• (((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                    •• ((ℓ2 ^-1 ▹▹ f₄) •• ℓ2^-1)))
             •• ((ℓ2 •• ((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                            •• ((ℓ2^-1 ▹▹ f₃) •• ℓ2^-1)) ▹▹ f₄)) •• ℓ2^-1)).
    Proof.
      eexists.
      cbn.
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
      apply idpath.
    Qed.

    Local Definition step2
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          p
          ((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
              •• ((ℓ2 ^-1 ▹▹ ℓ1) •• ℓ2^-1))
             •• (((ℓ2 •• (ℓ1 ◃◃ ℓ2)) •• disp_lassociator)
                   •• ((ℓ2^-1 ▹▹ f₄) •• ℓ2^-1)))
        =
        lassociator f₁ f₂ (f₃ · f₄) • lassociator (f₁ · f₂) f₃ f₄.
    Proof.
      eexists.
      refine (!_).
      cbn.
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step3
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step1)
          ((((ℓ2 •• (f₁ ◃◃ (((ℓ2 •• (f₂ ◃◃ ℓ2)) •• disp_lassociator)
                              •• ((ℓ2 ^-1 ▹▹ f₄) •• ℓ2 ^-1)))) •• ℓ2 ^-1)
              •• (((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                    •• ((ℓ2 ^-1 ▹▹ f₄) •• ℓ2^-1)))
             •• ((ℓ2 •• ((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                            •• ((ℓ2^-1 ▹▹ f₃) •• ℓ2^-1)) ▹▹ f₄)) •• ℓ2^-1))
        =
        transportf
          (λ z, _ ==>[ z ] _)
          p
          ((ℓ2 •• (f₁ ◃◃ (((ℓ2 •• (f₂ ◃◃ ℓ2)) •• disp_lassociator)
                            •• ((ℓ2 ^-1 ▹▹ f₄) •• ℓ2^-1))))
             •• ((((f₁ ◃◃ ℓ2) •• disp_lassociator)
                    •• ((ℓ2^-1 ▹▹ f₄) •• ℓ2^-1))
                   •• ((ℓ2 •• ((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                                  •• ((ℓ2^-1 ▹▹ f₃) •• ℓ2^-1)) ▹▹ f₄))
                         •• ℓ2^-1))).
    Proof.
      eexists.
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
                             exact (disp_vcomp_linv ℓ2).
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step4
      : ∑ p,
        transportf
          (λ z, _ ==>[ z ] _)
          (pr1 step3)
          ((ℓ2 •• (f₁ ◃◃ (((ℓ2 •• (f₂ ◃◃ ℓ2)) •• disp_lassociator)
                            •• ((ℓ2 ^-1 ▹▹ f₄) •• ℓ2^-1))))
             •• ((((f₁ ◃◃ ℓ2) •• disp_lassociator)
                    •• ((ℓ2^-1 ▹▹ f₄) •• ℓ2^-1))
                   •• ((ℓ2 •• ((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                                  •• ((ℓ2^-1 ▹▹ f₃) •• ℓ2^-1)) ▹▹ f₄))
                         •• ℓ2^-1)))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          ((ℓ2 •• (f₁ ◃◃ (((ℓ2 •• (f₂ ◃◃ ℓ2)) •• disp_lassociator)
                            •• ((ℓ2^-1 ▹▹ f₄) •• ℓ2^-1))))
             •• (((f₁ ◃◃ ℓ2) •• disp_lassociator)
                   •• ((ℓ2^-1 ▹▹ f₄)
                         •• (((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                                 •• ((ℓ2^-1 ▹▹ f₃) •• ℓ2^-1)) ▹▹ f₄)
                               •• ℓ2^-1)))).
    Proof.
      eexists.
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
                          exact (disp_vcomp_linv ℓ2).
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step5
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step4)
          ((ℓ2 •• (f₁ ◃◃ (((ℓ2 •• (f₂ ◃◃ ℓ2)) •• disp_lassociator)
                            •• ((ℓ2^-1 ▹▹ f₄) •• ℓ2^-1))))
             •• (((f₁ ◃◃ ℓ2) •• disp_lassociator)
                   •• ((ℓ2^-1 ▹▹ f₄)
                         •• (((((ℓ2 •• (f₁ ◃◃ ℓ2)) •• disp_lassociator)
                                 •• ((ℓ2^-1 ▹▹ f₃) •• ℓ2^-1)) ▹▹ f₄)
                               •• ℓ2^-1))))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          ((ℓ2 •• ((f₁ ◃◃ ℓ2)
                     •• (f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                  •• (disp_lassociator
                                        •• ((ℓ2^-1 ▹▹ f₄)
                                              •• ℓ2^-1))))))
             •• (((f₁ ◃◃ ℓ2) •• disp_lassociator)
                   •• ((ℓ2^-1 ▹▹ f₄)
                         •• (((((ℓ2 •• (f₁ ◃◃ ℓ2))
                                  •• disp_lassociator)
                                 •• ((ℓ2^-1 ▹▹ f₃)
                                       •• ℓ2^-1)) ▹▹ f₄)
                               •• ℓ2^-1)))).
    Proof.
      eexists.
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step6
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step5)
          ((ℓ2 •• ((f₁ ◃◃ ℓ2)
                     •• (f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                  •• (disp_lassociator
                                        •• ((ℓ2^-1 ▹▹ f₄)
                                              •• ℓ2^-1))))))
             •• (((f₁ ◃◃ ℓ2) •• disp_lassociator)
                   •• ((ℓ2^-1 ▹▹ f₄)
                         •• (((((ℓ2 •• (f₁ ◃◃ ℓ2))
                                  •• disp_lassociator)
                                 •• ((ℓ2^-1 ▹▹ f₃)
                                       •• ℓ2^-1)) ▹▹ f₄)
                               •• ℓ2^-1))))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2 •• ((f₁ ◃◃ ℓ2)
                    •• (((f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                   •• (disp_lassociator
                                         •• (ℓ2^-1 ▹▹ f₄))))
                           •• disp_lassociator)
                          •• ((ℓ2^-1 ▹▹ f₄)
                                •• (((((ℓ2
                                          •• (f₁ ◃◃ ℓ2))
                                         •• disp_lassociator)
                                        •• ((ℓ2^-1 ▹▹ f₃)
                                              •• ℓ2^-1)) ▹▹ f₄)
                                      •• ℓ2^-1))))).
    Proof.
      eexists.
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
                                        exact (disp_vcomp_linv ℓ2).
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step7
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step6)
          (ℓ2 •• ((f₁ ◃◃ ℓ2)
                    •• (((f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                   •• (disp_lassociator
                                         •• (ℓ2^-1 ▹▹ f₄))))
                           •• disp_lassociator)
                          •• ((ℓ2^-1 ▹▹ f₄)
                                •• (((((ℓ2
                                          •• (f₁ ◃◃ ℓ2))
                                         •• disp_lassociator)
                                        •• ((ℓ2^-1 ▹▹ f₃)
                                              •• ℓ2^-1)) ▹▹ f₄)
                                      •• ℓ2^-1)))))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2 •• ((f₁ ◃◃ ℓ2)
                    •• (((f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                   •• disp_lassociator))
                           •• (disp_lassociator
                                 •• ((f₁ ◃◃ ℓ2^-1) ▹▹ f₄)))
                          •• ((ℓ2^-1 ▹▹ f₄)
                                •• (((((ℓ2 •• (f₁ ◃◃ ℓ2))
                                         •• disp_lassociator)
                                        •• ((ℓ2^-1 ▹▹ f₃)
                                              •• ℓ2^-1)) ▹▹ f₄)
                                      •• ℓ2^-1))))).
    Proof.
      eexists.
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step8
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step7)
          (ℓ2 •• ((f₁ ◃◃ ℓ2)
                    •• (((f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                   •• disp_lassociator))
                           •• (disp_lassociator
                                 •• ((f₁ ◃◃ ℓ2^-1) ▹▹ f₄)))
                          •• ((ℓ2^-1 ▹▹ f₄)
                                •• (((((ℓ2 •• (f₁ ◃◃ ℓ2))
                                         •• disp_lassociator)
                                        •• ((ℓ2^-1 ▹▹ f₃)
                                              •• ℓ2^-1)) ▹▹ f₄)
                                      •• ℓ2^-1)))))
        =
        transportf (λ z, _ ==>[ z] _)
                   p
                   (ℓ2
                      •• ((f₁ ◃◃ ℓ2)
                            •• (((f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                           •• disp_lassociator))
                                   •• (disp_lassociator
                                         •• ((f₁ ◃◃ ℓ2 ^-1) ▹▹ f₄)))
                                  •• ((((((f₁ ◃◃ ℓ2)
                                            •• disp_lassociator)
                                           •• (ℓ2 ^-1 ▹▹ f₃))
                                          •• ℓ2 ^-1) ▹▹ f₄)
                                        •• ℓ2 ^-1)))).
    Proof.
      eexists.
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
                    etrans.
                    {
                      apply disp_vassocr.
                    }
                    apply maponpaths.
                    etrans.
                    {
                      apply disp_vassocr.
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
                          apply disp_vassocr.
                        }
                        apply maponpaths.
                        etrans.
                        {
                          apply maponpaths_2.
                          etrans.
                          {
                            apply disp_vassocr.
                          }
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths_2.
                            apply (disp_vcomp_linv ℓ2).
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
                          apply disp_mor_transportf_postwhisker.
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
                        apply disp_mor_transportf_postwhisker.
                      }
                      etrans.
                      {
                        apply maponpaths.
                        apply disp_mor_transportf_postwhisker.
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
                      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                    }
                    apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                  }
                  apply disp_rwhisker_transport_left_new.
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
            apply disp_mor_transportf_prewhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step9
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step8)
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• (((f₁ ◃◃ ((f₂ ◃◃ ℓ2)
                                  •• disp_lassociator))
                          •• (disp_lassociator
                                •• ((f₁ ◃◃ ℓ2 ^-1) ▹▹ f₄)))
                         •• ((((((f₁ ◃◃ ℓ2)
                                   •• disp_lassociator)
                                  •• (ℓ2 ^-1 ▹▹ f₃))
                                 •• ℓ2 ^-1) ▹▹ f₄)
                               •• ℓ2 ^-1))))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• ((f₁ ◃◃ ((f₂ ◃◃ ℓ2) •• disp_lassociator))
                         •• (disp_lassociator
                               •• ((((disp_lassociator
                                        •• (ℓ2 ^-1 ▹▹ f₃))
                                       •• ℓ2 ^-1) ▹▹ f₄)
                                     •• ℓ2 ^-1))))).
    Proof.
      eexists.
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
              refine (disp_vassocl _ _ _ @ _).
              apply maponpaths.
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
                        etrans.
                        {
                          apply disp_rwhisker_vcomp.
                        }
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
                                refine (disp_vassocr _ _ _ @ _).
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
                                      etrans.
                                      {
                                        etrans.
                                        {
                                          apply disp_lwhisker_vcomp.
                                        }
                                        apply maponpaths.
                                        etrans.
                                        {
                                          apply maponpaths.
                                          apply (disp_vcomp_linv ℓ2).
                                        }
                                        etrans.
                                        {
                                          apply disp_rwhisker_transport_right.
                                        }
                                        apply maponpaths.
                                        apply disp_lwhisker_id2.
                                      }
                                      apply (@transport_f_f
                                               _
                                               (λ z : _ ==> _, _ ==>[ z ] _)).
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
                                        apply disp_mor_transportf_postwhisker.
                                      }
                                      etrans.
                                      {
                                        apply maponpaths.
                                        apply disp_id2_left.
                                      }
                                      apply (@transport_f_f
                                               _ (λ z : _ ==> _, _ ==>[ z ] _)).
                                    }
                                    apply (@transport_f_f
                                             _ (λ z : _ ==> _, _ ==>[ z ] _)).
                                  }
                                  apply (@transport_f_f
                                           _ (λ z : _ ==> _, _ ==>[ z ] _)).
                                }
                                apply disp_mor_transportf_postwhisker.
                              }
                              apply (@transport_f_f
                                       _ (λ z : _ ==> _, _ ==>[ z ] _)).
                            }
                            apply disp_mor_transportf_postwhisker.
                          }
                          apply (@transport_f_f
                                   _ (λ z : _ ==> _, _ ==>[ z ] _)).
                        }
                        apply disp_rwhisker_transport_left_new.
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
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step10
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step9)
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• ((f₁ ◃◃ ((f₂ ◃◃ ℓ2) •• disp_lassociator))
                         •• (disp_lassociator
                               •• ((((disp_lassociator
                                        •• (ℓ2 ^-1 ▹▹ f₃))
                                       •• ℓ2 ^-1) ▹▹ f₄)
                                     •• ℓ2 ^-1)))))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• ((f₁ ◃◃ (f₂ ◃◃ ℓ2))
                         •• (((disp_lassociator •• disp_lassociator)
                                •• (((ℓ2 ^-1 ▹▹ f₃) •• ℓ2 ^-1) ▹▹ f₄))
                               •• ℓ2 ^-1)))).
    Proof.
      eexists.
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
                    refine (disp_vassocr _ _ _ @ _).
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      etrans.
                      {
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
                            apply disp_rwhisker_transport_left_new.
                          }
                          apply maponpaths.
                          apply disp_rwhisker_vcomp_alt.
                        }
                        etrans.
                        {
                          apply disp_mor_transportf_prewhisker.
                        }
                        etrans.
                        {
                          apply maponpaths.
                          apply disp_mor_transportf_prewhisker.
                        }
                        etrans.
                        {
                          apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                        }
                        apply maponpaths.
                        etrans.
                        {
                          refine (disp_vassocr _ _ _ @ _).
                          apply maponpaths.
                          etrans.
                          {
                            apply maponpaths_2.
                            apply disp_lassociator_lassociator.
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
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step11
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step10)
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• ((f₁ ◃◃ (f₂ ◃◃ ℓ2))
                         •• (((disp_lassociator •• disp_lassociator)
                                •• (((ℓ2 ^-1 ▹▹ f₃) •• ℓ2 ^-1) ▹▹ f₄))
                               •• ℓ2 ^-1))))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• ((((disp_lassociator •• (f₁;; f₂ ◃◃ ℓ2)) •• disp_lassociator)
                          •• (((ℓ2 ^-1 ▹▹ f₃) •• ℓ2 ^-1) ▹▹ f₄)) •• ℓ2 ^-1))).
    Proof.
      eexists.
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
              refine (disp_vassocr _ _ _ @ _).
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
                    etrans.
                    {
                      apply disp_vassocr.
                    }
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths_2.
                      apply disp_lwhisker_lwhisker.
                    }
                    apply disp_mor_transportf_postwhisker.
                  }
                  etrans.
                  {
                    etrans.
                    {
                      apply disp_mor_transportf_postwhisker.
                    }
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
        apply disp_mor_transportf_prewhisker.
      }
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step12
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step11)
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• ((((disp_lassociator •• (f₁;; f₂ ◃◃ ℓ2)) •• disp_lassociator)
                          •• (((ℓ2 ^-1 ▹▹ f₃) •• ℓ2 ^-1) ▹▹ f₄)) •• ℓ2 ^-1)))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• (((disp_lassociator •• (f₁;; f₂ ◃◃ ℓ2))
                          •• (((ℓ2 ^-1 ▹▹ f₃;; f₄)
                                 •• disp_lassociator)
                                •• (ℓ2 ^-1 ▹▹ f₄)))
                         •• ℓ2 ^-1))).
    Proof.
      eexists.
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
                refine (disp_vassocl _ _ _ @ _).
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
                        apply disp_rwhisker_rwhisker.
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
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Definition step13
      : ∑ p,
        transportf
          (λ z, _ ==>[ z] _)
          (pr1 step12)
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• (((disp_lassociator •• (f₁;; f₂ ◃◃ ℓ2))
                          •• (((ℓ2 ^-1 ▹▹ f₃;; f₄)
                                 •• disp_lassociator)
                                •• (ℓ2 ^-1 ▹▹ f₄)))
                         •• ℓ2 ^-1)))
        =
        transportf
          (λ z, _ ==>[ z] _)
          p
          (ℓ2
             •• ((f₁ ◃◃ ℓ2)
                   •• (((disp_lassociator •• (((ℓ2 ^-1 ▹▹ ℓ1) •• (ℓ1 ◃◃ ℓ2))
                                                •• disp_lassociator))
                          •• (ℓ2 ^-1 ▹▹ f₄))
                         •• ℓ2 ^-1))).
    Proof.
      eexists.
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
                refine (disp_vassocr _ _ _ @ _).
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
                      etrans.
                      {
                        refine (disp_vassocr _ _ _ @ _).
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
                    apply disp_mor_transportf_prewhisker.
                  }
                  apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
                }
                apply disp_mor_transportf_postwhisker.
              }
              apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
            }
            apply disp_mor_transportf_postwhisker.
          }
          apply disp_mor_transportf_prewhisker.
        }
        apply disp_mor_transportf_prewhisker.
      }
      apply (@transport_f_f _ (λ z : _ ==> _, _ ==>[ z ] _)).
    Qed.

    Local Arguments transportf {_} _ {_} {_} {_} _.

    Definition strict_fiber_bicat_data_laws_lassociator_lassociator
      : ((f₁ ◃ lassociator f₂ f₃ f₄)
           • lassociator f₁ (f₂ · f₃) f₄)
          • (lassociator f₁ f₂ f₃ ▹ f₄)
        =
        lassociator f₁ f₂ (f₃ · f₄) • lassociator (f₁ · f₂) f₃ f₄.
    Proof.
      refine (pr2 step1 @ _).
      refine (_ @ pr2 step2).
      refine (pr2 step3 @ _).
      refine (pr2 step4 @ _).
      refine (pr2 step5 @ _).
      refine (pr2 step6 @ _).
      refine (pr2 step7 @ _).
      refine (pr2 step8 @ _).
      refine (pr2 step9 @ _).
      refine (pr2 step10 @ _).
      refine (pr2 step11 @ _).
      refine (pr2 step12 @ _).
      refine (pr2 step13 @ _).
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
              refine (disp_vassocl _ _ _ @ _).
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
                    apply maponpaths_2.
                    apply disp_vassocl.
                  }
                  apply disp_mor_transportf_postwhisker.
                }
                apply disp_mor_transportf_prewhisker.
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
                        etrans.
                        {
                          refine (disp_vassocr _ _ _ @ _).
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
                                apply (disp_vcomp_linv ℓ2).
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
                apply disp_vassocr.
              }
              apply disp_mor_transportf_prewhisker.
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
      apply (@transportf_paths _ (λ α : id₁ c ==> id₁ c, _ ==>[ α] _)).
      apply cellset_property.
    Qed.
  End LassociatorLassociator.

  Definition strict_fiber_bicat_data_laws : prebicat_laws (strict_fiber_bicat_data D h c).
  Proof.
    repeat split.
    - exact (strict_fiber_bicat_data_laws_vcomp_left D h c).
    - exact (strict_fiber_bicat_data_laws_vcomp_right D h c).
    - exact (strict_fiber_bicat_data_laws_vcomp_assoc D h c).
    - exact (strict_fiber_bicat_data_laws_rwhisker_id2 D h c).
    - exact (strict_fiber_bicat_data_laws_id2_lwhisker D h c).
    - exact (strict_fiber_bicat_data_laws_vcomp_lwhisker D h c).
    - exact (strict_fiber_bicat_data_laws_vcomp_rwhisker D h c).
    - exact (strict_fiber_bicat_data_laws_vcomp_lunitor D h c).
    - exact (strict_fiber_bicat_data_laws_vcomp_runitor D h c).
    - exact (strict_fiber_bicat_data_laws_lwhisker_lwhisker D h c).
    - exact (strict_fiber_bicat_data_laws_rwhisker_lwhisker D h c).
    - exact (strict_fiber_bicat_data_laws_rwhisker_rwhisker D h c).
    - exact (strict_fiber_bicat_data_vcomp_whisker D h c).
    - exact (strict_fiber_bicat_data_laws_lunitor_linvunitor D h c).
    - exact (strict_fiber_bicat_data_laws_linvunitor_lunitor D h c).
    - exact (strict_fiber_bicat_data_laws_runitor_rinvunitor D h c).
    - exact (strict_fiber_bicat_data_laws_rinvunitor_runitor D h c).
    - exact (strict_fiber_bicat_data_laws_lassociator_rassociator D h c).
    - exact strict_fiber_bicat_data_laws_rassociator_lassociator.
    - exact strict_fiber_bicat_data_laws_runitor_rwhisker.
    - exact strict_fiber_bicat_data_laws_lassociator_lassociator.
  Qed.

  Definition strict_fiber_bicat : prebicat.
  Proof.
    use tpair.
    - exact (strict_fiber_bicat_data D h c).
    - exact strict_fiber_bicat_data_laws.
  Defined.
End LocalIsoFibration.
