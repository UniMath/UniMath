(*********************************************************************************

 Displayed monoidal categories

 In this file, we define the notion of a displayed monoidal category. The style of
 the definition is similar to the definition of a monoidal category.

Note: after refactoring on March 10, 2023, the prior Git history of this development is found via
git log -- UniMath/CategoryTheory/Monoidal/DisplayedMonoidalWhiskered.v

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import MonoidalNotations.
Import DisplayedBifunctorNotations.

Section DisplayedMonoidalCategories.

  Definition disp_tensor
             {C : category}
             (D : disp_cat C)
             (M : monoidal C)
    : UU
    := disp_bifunctor M D D D.

  Identity Coercion disptensor_into_dispbifunctor : disp_tensor >-> disp_bifunctor.

  Definition disp_leftunitor_data
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DT : disp_tensor D M)
             (i : D I_{M})
    : UU
    := ∏ (x : C) (xx : D x), i ⊗⊗_{DT} xx -->[lu^{M}_{x}] xx.

  Definition disp_leftunitorinv_data
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DT : disp_tensor D M)
             (i : D I_{M})
    : UU
    := ∏ (x : C) (xx : D x), xx -->[luinv^{M}_{x}] i ⊗⊗_{DT} xx.

  Definition disp_rightunitor_data
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DT : disp_tensor D M)
             (i : D I_{M})
    : UU
    := ∏ (x : C) (xx : D x), xx ⊗⊗_{DT} i -->[ru^{M}_{x}] xx.

  Definition disp_rightunitorinv_data
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DT : disp_tensor D M)
             (i : D I_{M})
    : UU
    := ∏ (x : C) (xx : D x), xx -->[ruinv^{M}_{x}] xx ⊗⊗_{DT} i.

  Definition disp_associator_data
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DT : disp_tensor D M)
    : UU
    := ∏ (x y z : C) (xx : D x) (yy : D y) (zz : D z),
       (xx ⊗⊗_{DT} yy) ⊗⊗_{DT} zz
       -->[α^{M}_{x,y,z}]
       xx ⊗⊗_{DT} (yy ⊗⊗_{DT} zz).

  Definition disp_associatorinv_data
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DT : disp_tensor D M)
    : UU
    := ∏ (x y z : C) (xx : D x) (yy : D y) (zz : D z),
       xx ⊗⊗_{DT} (yy ⊗⊗_{DT} zz)
       -->[αinv_{M} x y z]
       (xx ⊗⊗_{DT} yy) ⊗⊗_{DT} zz.

  Definition disp_monoidal_data
             {C : category}
             (D : disp_cat C)
             (M : monoidal C)
    : UU
    := ∑ (DT : disp_tensor D M)
         (i : D I_{M}),
       (disp_leftunitor_data DT i)
       × (disp_leftunitorinv_data DT i)
       × (disp_rightunitor_data DT i)
       × (disp_rightunitorinv_data DT i)
       × (disp_associator_data DT)
       × (disp_associatorinv_data DT).

  Definition make_disp_monoidal_data_groupoidal
             {C : category}
             (D : disp_cat C)
             (gdisp : groupoidal_disp_cat D)
             (M : monoidal C)
             (DT : disp_tensor D M)
             (i : D I_{M})
             (dlu : disp_leftunitor_data DT i)
             (dru : disp_rightunitor_data DT i)
             (dα : disp_associator_data DT)
    : disp_monoidal_data D M.
  Proof.
    exists DT. exists i. exists dlu.
    use tpair.
    { intros x xx.
      set (aux := gdisp _ _ _ (pr2 (leftunitor_nat_z_iso M) x) _ _ (dlu x xx)).
      exact (pr1 aux).
    }
    exists dru.
    use tpair.
    { intros x xx.
      set (aux := gdisp _ _ _ (pr2 (rightunitor_nat_z_iso M) x) _ _ (dru x xx)).
      exact (pr1 aux).
    }
    exists dα.
    intros x y z xx yy zz.
    set (aux := gdisp _ _ _ (pr2 (z_iso_from_associator_iso M x y z)) _ _ (dα x y z xx yy zz)).
    exact (pr1 aux).
  Defined.

  Definition disp_monoidal_tensor
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_tensor D M
    := pr1 DMD.

  Coercion disp_monoidal_tensor : disp_monoidal_data >-> disp_tensor.

  Definition disp_monoidal_unit
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : D I_{M}
    := pr12 DMD.

  Notation "dI_{ DMD }" := (disp_monoidal_unit DMD).

  Definition disp_monoidal_leftunitor
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_leftunitor_data DMD dI_{DMD}
    := pr122 DMD.

  Notation "dlu_{ DMD }" := (disp_monoidal_leftunitor DMD).

  Definition disp_monoidal_leftunitorinv
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_leftunitorinv_data DMD dI_{DMD}
    := pr1 (pr222 DMD).

  Notation "dluinv_{ DMD }" := (disp_monoidal_leftunitorinv DMD).

  Definition disp_monoidal_rightunitor
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_rightunitor_data DMD dI_{DMD}
    := pr12 (pr222 DMD).

  Notation "dru_{ DMD }" := (disp_monoidal_rightunitor DMD).

  Definition disp_monoidal_rightunitorinv
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_rightunitorinv_data DMD dI_{DMD}
    := pr122 (pr222 DMD).

  Notation "druinv_{ DMD }" := (disp_monoidal_rightunitorinv DMD).

  Definition disp_monoidal_associator
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_associator_data DMD
    := pr1 (pr222 (pr222 DMD)).

  Notation "dα_{ DMD }" := (disp_monoidal_associator DMD).

  Definition disp_monoidal_associatorinv
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_associatorinv_data DMD
    := pr2 (pr222 (pr222 DMD)).

  Notation "dαinv_{ DMD }" := (disp_monoidal_associatorinv DMD).

  (** PROPERTIES **)

  Definition disp_leftunitor_nat
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dlu : disp_leftunitor_data DT i)
    : UU
    := ∏ (x y : C)
         (f : C⟦x,y⟧)
         (xx : D x) (yy : D y)
         (ff : xx -->[f] yy),
       (i ⊗⊗^{DT}_{l} ff) ;; (dlu y yy)
       =
       transportb
         _
         (pr1 (monoidal_leftunitorlaw M) _ _ _)
         (dlu x xx ;; ff).

  Definition disp_leftunitor_iso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dlu : disp_leftunitor_data DT i)
             (dluinv : disp_leftunitorinv_data DT i)
    : UU
    := ∏ (x : C) (xx : D x),
       is_disp_inverse
         (pr2 (monoidal_leftunitorlaw M) x)
         (dlu x xx)
         (dluinv x xx).

  Definition disp_leftunitor_law
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dlu : disp_leftunitor_data DT i)
             (dluinv : disp_leftunitorinv_data DT i)
    : UU
    := disp_leftunitor_nat dlu × disp_leftunitor_iso dlu dluinv.

  Definition disp_leftunitorlaw_nat
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             {dlu : disp_leftunitor_data DT i}
             {dluinv : disp_leftunitorinv_data DT i}
             (dlun : disp_leftunitor_law dlu dluinv)
    : disp_leftunitor_nat dlu
    := pr1 dlun.

  Definition disp_leftunitorlaw_iso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             {dlu : disp_leftunitor_data DT i}
             {dluinv : disp_leftunitorinv_data DT i}
             (dlui : disp_leftunitor_law dlu dluinv)
    : disp_leftunitor_iso dlu dluinv
    := pr2 dlui.

  Definition disp_rightunitor_nat
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dru : disp_rightunitor_data DT i)
    : UU
    := ∏ (x y : C)
         (f : C⟦x,y⟧)
         (xx : D x) (yy : D y)
         (ff : xx -->[f] yy),
       (ff ⊗⊗^{DT}_{r} i) ;; (dru y yy)
       =
       transportb
         _
         (pr1 (monoidal_rightunitorlaw M) _ _ _)
         (dru x xx ;; ff).

  Definition disp_rightunitor_iso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dru : disp_rightunitor_data DT i)
             (druinv : disp_rightunitorinv_data DT i)
    : UU
    := ∏ (x : C) (xx : D x),
       is_disp_inverse
         (pr2 (monoidal_rightunitorlaw M) x)
         (dru x xx)
         (druinv x xx).

  Definition disp_rightunitor_law
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dru : disp_rightunitor_data DT i)
             (druinv : disp_rightunitorinv_data DT i)
    : UU
    := disp_rightunitor_nat dru × disp_rightunitor_iso dru druinv.

  Definition disp_rightunitorlaw_nat
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             {dru : disp_rightunitor_data DT i}
             {druinv : disp_rightunitorinv_data DT i}
             (drun : disp_rightunitor_law dru druinv)
    : disp_rightunitor_nat dru
    := pr1 drun.

  Definition disp_rightunitorlaw_iso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             {dru : disp_rightunitor_data DT i}
             {druinv : disp_rightunitorinv_data DT i}
             (drui : disp_rightunitor_law dru druinv)
    : disp_rightunitor_iso dru druinv
    := pr2 drui.

  Definition disp_associator_nat_leftwhisker
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             (dα : disp_associator_data DT)
    : UU
    := ∏ (x y z1 z2 : C)
         (h : C⟦z1,z2⟧)
         (xx : D x)
         (yy : D y)
         (zz1 : D z1)
         (zz2 : D z2)
         (hh : zz1-->[h] zz2),
       (dα _ _ _ xx yy zz1) ;; (xx ⊗⊗^{DT}_{l} (yy ⊗⊗^{DT}_{l} hh))
       =
       transportb
         _
         ((associatorlaw_natleft (monoidal_associatorlaw M)) x y z1 z2 h)
         (((xx ⊗⊗_{DT} yy) ⊗⊗^{DT}_{l} hh) ;; (dα _ _ _ xx yy zz2)).

  Definition disp_associator_nat_rightwhisker
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             (dα : disp_associator_data DT)
    : UU
    := ∏ (x1 x2 y z : C)
         (f : C⟦x1,x2⟧)
         (xx1 : D x1) (xx2 : D x2) (yy : D y) (zz : D z)
         (ff : xx1-->[f] xx2),
       (dα _ _ _ xx1 yy zz) ;; (ff ⊗⊗^{DT}_{r} (yy ⊗⊗_{DT} zz))
       =
       transportb
         _
         ((associatorlaw_natright (monoidal_associatorlaw M)) x1 x2 y z f)
         (((ff ⊗⊗^{DT}_{r} yy) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ xx2 yy zz)).

  Definition disp_associator_nat_leftrightwhisker
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             (dα : disp_associator_data DT)
    : UU
    := ∏ (x y1 y2 z : C)
         (g : C⟦y1,y2⟧)
         (xx : D x) (yy1 : D y1) (yy2 : D y2) (zz : D z)
         (gg : yy1-->[g] yy2),
       (dα _ _ _ xx yy1 zz) ;; (xx ⊗⊗^{DT}_{l} (gg ⊗⊗^{DT}_{r} zz))
       =
       transportb
         _
         ((associatorlaw_natleftright (monoidal_associatorlaw M)) x y1 y2 z g)
         (((xx ⊗⊗^{DT}_{l} gg) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ xx yy2 zz)).

  Definition disp_associator_nat'
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {dα : disp_associator_data DT}
             (dtl :  disp_associator_nat_leftwhisker dα)
             (dtr : disp_associator_nat_rightwhisker dα)
             (dtlr : disp_associator_nat_leftrightwhisker dα)
    : ∏ (x1 x2 y1 y2 z1 z2 : C)
        (xx1 : D x1) (xx2 : D x2)
        (yy1 : D y1) (yy2 : D y2)
        (zz1 : D z1) (zz2 : D z2)
        (f : C⟦x1,x2⟧)
        (g : C⟦y1,y2⟧)
        (h : C⟦z1,z2⟧)
        (ff : xx1-->[f] xx2)
        (gg : yy1 -->[g] yy2)
        (hh : zz1 -->[h] zz2),
       ((dα _ _ _ xx1 yy1 zz1) ;; (ff ⊗⊗^{DT} (gg ⊗⊗^{DT} hh)))
       =
       transportb
         _
         (associator_nat2
            M
            f g h)
         (((ff ⊗⊗^{DT} gg) ⊗⊗^{DT} hh) ;; dα _ _ _ xx2 yy2 zz2).
  Proof.
    intros.
    unfold dispfunctoronmorphisms1.
    etrans. { apply assoc_disp. }
    rewrite dtr.
    etrans. {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite transport_b_f.
    apply transportf_transpose_left.
    etrans. { apply assoc_disp_var. }
    apply transportf_transpose_left.
    rewrite transport_b_b.
    rewrite transport_b_b.

    etrans. {
      apply maponpaths_1.
      apply maponpaths_1.
      apply disp_bifunctor_leftcomp.
    }
    etrans. {
      apply maponpaths.
      apply mor_disp_transportf_prewhisker.
    }
    etrans. {
      apply maponpaths_1.
      rewrite assoc_disp.
      rewrite dtlr.
      apply transport_f_b.
    }

    etrans. {
      apply maponpaths.
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    etrans. {
      apply maponpaths.
      apply transport_f_f.
    }
    etrans. { apply mor_disp_transportf_prewhisker. }
    apply transportf_transpose_left.

    etrans.
    {
      apply maponpaths_1.
      rewrite assoc_disp_var.
      apply maponpaths_1.
      apply maponpaths_1.
      apply dtl.
    }
    etrans. { apply mor_disp_transportf_prewhisker. }
    apply transportf_transpose_left.
    etrans. {
      apply maponpaths.
      apply mor_disp_transportf_prewhisker.
    }
    etrans. { apply mor_disp_transportf_prewhisker. }
    apply transportf_transpose_left.
    rewrite assoc_disp.
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply (pathsinv0
               (transportb_transpose_left
                  (disp_bifunctor_rightcomp DT _ _ _ _ _ _ _ _ _ _ _ _))).
    }
    rewrite transport_b_b.
    rewrite transport_b_b.
    rewrite transport_b_b.
    etrans. {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite transport_b_f.
    apply transportf_transpose_left.
    rewrite transport_b_b.

    etrans. { apply assoc_disp. }
    apply transportb_transpose_left.


    use pathsinv0.
    rewrite transport_f_b.
    apply transportf_set.
    apply homset_property.
  Qed.

  Definition disp_associator_iso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             (dα : disp_associator_data DT)
             (dαinv : disp_associatorinv_data DT)
    : UU
    := ∏ (x y z : C)
         (xx : D x)
         (yy : D y)
         (zz : D z),
       is_disp_inverse
         (pr222 (monoidal_associatorlaw M) x y z)
         (dα _ _ _ xx yy zz)
         (dαinv _ _ _ xx yy zz).

  Definition disp_associator_law
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             (dα : disp_associator_data DT)
             (dαinv : disp_associatorinv_data DT)
    : UU
    := (disp_associator_nat_leftwhisker dα)
       × (disp_associator_nat_rightwhisker dα)
       × (disp_associator_nat_leftrightwhisker dα)
       × (disp_associator_iso dα dαinv).

  Definition disp_associatorlaw_natleft
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {dα : disp_associator_data DT}
             {dαinv : disp_associatorinv_data DT}
             (dαl : disp_associator_law dα dαinv)
    : disp_associator_nat_leftwhisker dα
    := pr1 dαl.

  Definition disp_associatorlaw_natright
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {dα : disp_associator_data DT}
             {dαinv : disp_associatorinv_data DT}
             (dαl : disp_associator_law dα dαinv)
    : disp_associator_nat_rightwhisker dα
    := pr12 dαl.

  Definition disp_associatorlaw_natleftright
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {dα : disp_associator_data DT}
             {dαinv : disp_associatorinv_data DT}
             (dαl : disp_associator_law dα dαinv)
    : disp_associator_nat_leftrightwhisker dα
    := pr122 dαl.

  Definition disp_associatorlaw_iso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {dα : disp_associator_data DT}
             {dαinv : disp_associatorinv_data DT}
             (dαl : disp_associator_law dα dαinv)
    : disp_associator_iso dα dαinv
    := pr222 dαl.

  Definition disp_triangle_identity
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             {i : D I_{M}}
             (dlu : disp_leftunitor_data DT i)
             (dru : disp_rightunitor_data DT i)
             (dα : disp_associator_data DT)
    : UU
    := ∏ (x y : C) (xx : D x) (yy : D y),
       ((dα x I_{M} y xx i yy) ;; (xx ⊗⊗^{DT}_{l} dlu y yy ))
       =
       transportb
         _
         ((monoidal_triangleidentity M) x y)
         ((dru x xx) ⊗⊗^{DT}_{r} yy).

  Definition disp_pentagon_identity
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             {DT : disp_tensor D M}
             (dα : disp_associator_data DT)
    : UU
    := ∏ (w x y z : C)
         (ww : D w)
         (xx : D x)
         (yy : D y)
         (zz : D z),
       ((dα _ _ _ ww xx yy) ⊗⊗^{DT}_{r} zz)
       ;; (dα _ _ _ ww (xx ⊗⊗_{DT} yy) zz)
       ;; (ww ⊗⊗^{DT}_{l} (dα _ _ _ xx yy zz))
       =
       transportb
         _
         ((monoidal_pentagonidentity M) w x y z)
         ((dα _ _ _ (ww ⊗⊗_{DT} xx) yy zz) ;; (dα _ _ _ ww xx (yy ⊗⊗_{DT} zz))).

  Definition disp_monoidal_laws
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : UU
    := (disp_leftunitor_law dlu_{DMD} dluinv_{DMD})
       × (disp_rightunitor_law dru_{DMD} druinv_{DMD})
       × (disp_associator_law dα_{DMD} dαinv_{DMD})
       × (disp_triangle_identity dlu_{DMD} dru_{DMD} dα_{DMD})
       × (disp_pentagon_identity dα_{DMD}).

  Definition disp_monoidal
             {C : category}
             (D : disp_cat C)
             (M : monoidal C)
    : UU
    := ∑ (MD : disp_monoidal_data D M), (disp_monoidal_laws MD).

  Definition make_disp_monoidal_locally_prop
             {C : category}
             {D : disp_cat C}
             (LP : locally_propositional D)
             {M : monoidal C}
             (DMD : disp_monoidal_data D M)
    : disp_monoidal D M.
  Proof.
    exists DMD.
    abstract (repeat split ; try intro ; intros ; apply LP).
  Defined.

  Definition make_disp_monoidal_groupoidal
             {C : category}
             {D : disp_cat C}
             (gdisp : groupoidal_disp_cat D)
             {M : monoidal C}
             (DT : disp_tensor D M)
             (i : D I_{M})
             (dlu : disp_leftunitor_data DT i)
             (dru : disp_rightunitor_data DT i)
             (dα : disp_associator_data DT) :
    let DMD := make_disp_monoidal_data_groupoidal D gdisp M DT i dlu dru dα in
           ∏ (dlu_nat : disp_leftunitor_nat dlu_{DMD})
             (dru_nat : disp_rightunitor_nat dru_{DMD})
             (dα_nat_left : disp_associator_nat_leftwhisker dα_{DMD})
             (dα_nat_right : disp_associator_nat_rightwhisker dα_{DMD})
             (dα_nat_left_right : disp_associator_nat_leftrightwhisker dα_{DMD})
             (dtriangle : disp_triangle_identity dlu_{DMD} dru_{DMD} dα_{DMD})
             (dpentagon : disp_pentagon_identity dα_{DMD}),
      disp_monoidal D M.
  Proof.
    intros.
    use tpair.
    - exact DMD.
    - split5.
      + split.
        * exact dlu_nat.
        * intros x xx.
          set (aux := gdisp _ _ _ (pr2 (leftunitor_nat_z_iso M) x) _ _ (dlu x xx)).
          exact (pr2 aux).
      + split.
        * exact dru_nat.
        * intros x xx.
          set (aux := gdisp _ _ _ (pr2 (rightunitor_nat_z_iso M) x) _ _ (dru x xx)).
          exact (pr2 aux).
      + split4.
        * exact dα_nat_left.
        * exact dα_nat_right.
        * exact dα_nat_left_right.
        * intros x y z xx yy zz.
          set (aux := gdisp _ _ _ (pr2 (z_iso_from_associator_iso M x y z)) _ _ (dα x y z xx yy zz)).
          exact (pr2 aux).
      + exact dtriangle.
      + exact dpentagon.
  Defined.

  Definition disp_monoidal_mondata
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_monoidal_data D M
    := pr1 DM.

  Coercion disp_monoidal_mondata : disp_monoidal >-> disp_monoidal_data.

  Definition disp_monoidal_monlaws
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_monoidal_laws DM
    := pr2 DM.

  Definition disp_monoidal_leftunitorlaw
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_leftunitor_law dlu_{DM} dluinv_{DM}
    := pr1 (disp_monoidal_monlaws DM).

  Definition disp_monoidal_leftunitornat
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_leftunitor_nat dlu_{DM}
    := disp_leftunitorlaw_nat (disp_monoidal_leftunitorlaw DM).

  Definition disp_monoidal_leftunitoriso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_leftunitor_iso dlu_{DM} dluinv_{DM}
    := disp_leftunitorlaw_iso (disp_monoidal_leftunitorlaw DM).

  Definition disp_monoidal_rightunitorlaw
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_rightunitor_law dru_{DM} druinv_{DM}
    := pr12 (disp_monoidal_monlaws DM).

  Definition disp_monoidal_rightunitornat
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_rightunitor_nat dru_{DM}
    := disp_rightunitorlaw_nat (disp_monoidal_rightunitorlaw DM).

  Definition disp_monoidal_rightunitoriso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_rightunitor_iso dru_{DM} druinv_{DM}
    := disp_rightunitorlaw_iso (disp_monoidal_rightunitorlaw DM).

  Definition disp_monoidal_associatorlaw
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_associator_law dα_{DM} dαinv_{DM}
    := pr122 (disp_monoidal_monlaws DM).

  Definition disp_monoidal_associatornatleft
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_associator_nat_leftwhisker dα_{DM}
    := disp_associatorlaw_natleft (disp_monoidal_associatorlaw DM).

  Definition disp_monoidal_associatornatright
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_associator_nat_rightwhisker dα_{DM}
    := disp_associatorlaw_natright (disp_monoidal_associatorlaw DM).

  Definition disp_monoidal_associatornatleftright
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_associator_nat_leftrightwhisker dα_{DM}
    := disp_associatorlaw_natleftright (disp_monoidal_associatorlaw DM).

  Definition disp_monoidal_associatoriso
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_associator_iso dα_{DM} dαinv_{DM}
    := disp_associatorlaw_iso (disp_monoidal_associatorlaw DM).

  Definition disp_monoidal_triangleidentity
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_triangle_identity dlu_{DM} dru_{DM} dα_{DM}
    := pr1 (pr222 (disp_monoidal_monlaws DM)).

  Definition disp_monoidal_pentagonidentity
             {C : category}
             {D : disp_cat C}
             {M : monoidal C}
             (DM : disp_monoidal D M)
    : disp_pentagon_identity dα_{DM}
    := pr2 (pr222 (disp_monoidal_monlaws DM)).

  Lemma isaprop_disp_monoidal_laws
        {C : category}
        {D : disp_cat C}
        {M : monoidal C}
        (DM : disp_monoidal_data D M)
    : isaprop (disp_monoidal_laws DM).
  Proof.
    repeat (apply isapropdirprod)
    ; repeat (apply impred ; intro)
    ; repeat (try apply D)
    ; repeat (apply isaprop_is_disp_inverse).
  Qed.
End DisplayedMonoidalCategories.

Module DisplayedMonoidalNotations.
  Notation "dI_{ M }" := (disp_monoidal_unit M).
  Notation "dlu^{ M }" := (disp_monoidal_leftunitor M).
  Notation "dru^{ M }" := (disp_monoidal_rightunitor M).
  Notation "dα^{ M }" := (disp_monoidal_associator M).

  Notation "dluinv^{ M }" := (disp_monoidal_leftunitorinv M).
  Notation "druinv^{ M }" := (disp_monoidal_rightunitorinv M).
  Notation "dαinv^{ M }" := (disp_monoidal_associatorinv M).

  Notation "dlu^{ M }_{ xx }" := (disp_monoidal_leftunitor M _ xx).
  Notation "dru^{ M }_{ xx }" := (disp_monoidal_rightunitor M _ xx).
  Notation "dα^{ M }_{ xx , yy , zz }" := (disp_monoidal_associator M _ _ _ xx yy zz).

  Notation "dluinv^{ M }_{ xx }" := (disp_monoidal_leftunitorinv M _ xx).
  Notation "druinv^{ M }_{ xx }" := (disp_monoidal_rightunitorinv M _ xx).
  Notation "dαinv^{ M }_{ xx , yy , zz }" := (disp_monoidal_associatorinv M _ _ _ xx yy zz).
End DisplayedMonoidalNotations.
