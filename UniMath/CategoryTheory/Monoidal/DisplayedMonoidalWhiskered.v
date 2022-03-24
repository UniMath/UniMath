Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import MonoidalNotations.
Import DisplayedBifunctorNotations.

Section DisplayedMonoidalCategories.

  Definition disp_tensor {C : category} (D : disp_cat C) (M : monoidal C) : UU := disp_bifunctor M D D D.
  Identity Coercion disptensor_into_dispbifunctor : disp_tensor >-> disp_bifunctor.

  Definition disp_associator_data {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : UU :=
    ∏ (x y z : C), ∏ (xx : D x) (yy : D y) (zz : D z),
      ((xx ⊗⊗_{DT} yy) ⊗⊗_{DT} zz) -->[α^{M}_{x,y,z}] (xx ⊗⊗_{DT} (yy ⊗⊗_{DT} zz)).

  Definition disp_leftunitor_data {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) (i : D I_{M}) : UU :=
    ∏ (x : C) (xx : D x), i ⊗⊗_{DT} xx -->[lu^{M}_{x}] xx.

  Lemma dispnattransdata_from_displeftunitordata {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor_data DT i) :
    disp_nat_trans_data (nattransdata_from_leftunitordata lu_{M}) (leftwhiskering_dispfunctor DT (disp_bifunctor_leftid DT) (disp_bifunctor_leftcomp DT) I_{M} i) (disp_functor_identity D).
  Proof.
    exact (λ x xx, dlu x xx).
  Defined.

  Definition disp_rightunitor_data {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) (i : D I_{M}) : UU :=
    ∏ (x : C) (xx : D x), xx ⊗⊗_{DT} i -->[ru^{M}_{x}] xx.

  Lemma dispnattransdata_from_rightunitordata {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dru : disp_rightunitor_data DT i) :
    disp_nat_trans_data (nattransdata_from_rightunitordata ru_{M}) (rightwhiskering_dispfunctor DT (disp_bifunctor_rightid DT) (disp_bifunctor_rightcomp DT) I_{M} i) (disp_functor_identity D).
  Proof.
    exact (λ x xx, dru x xx).
  Defined.

  Definition disp_monoidal_data {C : category} (D : disp_cat C) (M : monoidal C) : UU :=
    ∑ DT : disp_tensor D M, ∑ i : D I_{M},
          (disp_leftunitor_data DT i) × (disp_rightunitor_data DT i) × (disp_associator_data DT).

  Definition disp_monoidal_tensor {C : category} {D : disp_cat C} {M : monoidal C} (DMD : disp_monoidal_data D M) : disp_tensor D M := pr1 DMD.
  Coercion disp_monoidal_tensor : disp_monoidal_data >-> disp_tensor.

  Definition disp_monoidal_unit {C : category} {D : disp_cat C} {M : monoidal C} (DMD : disp_monoidal_data D M) : D I_{M} := pr1 (pr2 DMD).
  Notation "dI_{ DMD }" := (disp_monoidal_unit DMD).

  Definition disp_monoidal_leftunitor {C : category} {D : disp_cat C} {M : monoidal C} (DMD : disp_monoidal_data D M) : disp_leftunitor_data DMD dI_{DMD} := pr1 (pr2 (pr2 DMD)).
  Notation "dlu_{ DMD }" := (disp_monoidal_leftunitor DMD).

  Definition disp_monoidal_rightunitor {C : category} {D : disp_cat C} {M : monoidal C} (DMD : disp_monoidal_data D M) : disp_rightunitor_data DMD dI_{DMD} := pr1 (pr2 (pr2 (pr2 DMD))).
  Notation "dru_{ DMD }" := (disp_monoidal_rightunitor DMD).

  Definition disp_monoidal_associator {C : category} {D : disp_cat C} {M : monoidal C} (DMD : disp_monoidal_data D M) : disp_associator_data DMD := pr2 (pr2 (pr2 (pr2 DMD))).
  Notation "dα_{ DMD }" := (disp_monoidal_associator DMD).

  (** PROPERTIES **)
  Definition disp_associator_nat_leftwhisker {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
  := ∏ (x y z1 z2 : C) (h : C⟦z1,z2⟧) (xx : D x) (yy : D y) (zz1 : D z1) (zz2 : D z2) (hh : zz1-->[h] zz2),
      (dα _ _ _ xx yy zz1) ;; (xx ⊗⊗^{DT}_{l} (yy ⊗⊗^{DT}_{l} hh)) = transportb _ ((associatorlaw_natleft (monoidal_associatorlaw M)) x y z1 z2 h) (((xx ⊗⊗_{DT} yy) ⊗⊗^{DT}_{l} hh) ;; (dα _ _ _ xx yy zz2)).

  Definition disp_associator_nat_rightwhisker {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
  := ∏ (x1 x2 y z : C) (f : C⟦x1,x2⟧) (xx1 : D x1) (xx2 : D x2) (yy : D y) (zz : D z) (ff : xx1-->[f] xx2),
    (dα _ _ _ xx1 yy zz) ;; (ff ⊗⊗^{DT}_{r} (yy ⊗⊗_{DT} zz)) = transportb _ ((associatorlaw_natright (monoidal_associatorlaw M)) x1 x2 y z f) (((ff ⊗⊗^{DT}_{r} yy) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ xx2 yy zz)).

  Definition disp_associator_nat_leftrightwhisker {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
  := ∏ (x y1 y2 z : C) (g : C⟦y1,y2⟧) (xx : D x) (yy1 : D y1) (yy2 : D y2) (zz : D z) (gg : yy1-->[g] yy2),
      (dα _ _ _ xx yy1 zz) ;; (xx ⊗⊗^{DT}_{l} (gg ⊗⊗^{DT}_{r} zz)) = transportb _ ((associatorlaw_natleftright (monoidal_associatorlaw M)) x y1 y2 z g) (((xx ⊗⊗^{DT}_{l} gg) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ xx yy2 zz)).

  Definition disp_associator_nat' {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dtl :  disp_associator_nat_leftwhisker dα) (dtr : disp_associator_nat_rightwhisker dα) (dtlr : disp_associator_nat_leftrightwhisker dα) :
    ∏ (x1 x2 y1 y2 z1 z2 : C), ∏ (xx1 : D x1) (xx2 : D x2) (yy1 : D y1) (yy2 : D y2) (zz1 : D z1) (zz2 : D z2),
      ∏ (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧) (h : C⟦z1,z2⟧), ∏ (ff : xx1-->[f] xx2) (gg : yy1 -->[g] yy2) (hh : zz1 -->[h] zz2),
      ((dα _ _ _ xx1 yy1 zz1) ;; (ff ⊗⊗^{DT} (gg ⊗⊗^{DT} hh))) =
        transportb _ (associator_nat2
                   (associatorlaw_natleft (monoidal_associatorlaw M))
                   (associatorlaw_natright (monoidal_associatorlaw M))
                   (associatorlaw_natleftright (monoidal_associatorlaw M))
                   f g h)
             (((ff ⊗⊗^{DT} gg) ⊗⊗^{DT} hh) ;; dα _ _ _ xx2 yy2 zz2).
  Proof.
    intros.
    unfold dispfunctoronmorphisms1.
    etrans. { apply assoc_disp. }
    rewrite dtr.
    rewrite mor_disp_transportb_postwhisker.
    rewrite transport_b_b.
    apply transportb_transpose_left.
    etrans. { apply assoc_disp_var. }
    rewrite transport_f_b.
    apply transportf_transpose_left.
    rewrite transport_b_f.
    etrans. {
      apply maponpaths_1.
      apply maponpaths_1.
      apply disp_bifunctor_leftcomp.
    }
    rewrite mor_disp_transportb_prewhisker.
    rewrite mor_disp_transportb_prewhisker.
    apply transportb_transpose_left.
    etrans. {
      apply maponpaths_1.
      rewrite assoc_disp.
      rewrite dtlr.
      rewrite mor_disp_transportb_postwhisker.
      apply transport_b_b.
    }
    rewrite mor_disp_transportb_prewhisker.
    apply transportf_transpose_left.

    etrans.
    {
      apply maponpaths_1.
      rewrite assoc_disp_var.
      apply maponpaths_1.
      apply maponpaths_1.
      apply dtl.
    }

    rewrite mor_disp_transportb_prewhisker.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportb_prewhisker.
    rewrite transport_f_b.
    apply transportf_transpose_left.
    rewrite transport_b_b.
    rewrite transport_f_f.
    rewrite transport_b_f.

    use pathsinv0.
    apply transportf_transpose_left.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_2.
      apply disp_bifunctor_rightcomp.
    }

    rewrite mor_disp_transportb_postwhisker.
    rewrite mor_disp_transportb_postwhisker.
    apply transportb_transpose_left.
    rewrite transport_f_b.
    etrans. { apply assoc_disp_var. }
    apply transportf_transpose_left.
    rewrite transport_b_f.
    use pathsinv0.
    apply transportf_transpose_left.
    etrans. { apply assoc_disp. }
    apply transportb_transpose_left.
    rewrite transport_f_b.
    use pathsinv0.
    apply transportf_set.
    apply homset_property.
  Qed.

  Definition disp_associator_iso {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU :=
    ∏ (x y z : C), ∏ (xx : D x) (yy : D y) (zz : D z), is_z_iso_disp
        ((α^{M}_{x,y,z}),,((associatorlaw_iso (monoidal_associatorlaw M)) x y z)) (dα _ _ _ xx yy zz).

  Definition disp_associator_law  {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU :=
  (disp_associator_nat_leftwhisker dα) × (disp_associator_nat_rightwhisker dα) × (disp_associator_nat_leftrightwhisker dα) × (disp_associator_iso dα).

  Definition disp_associatorlaw_natleft {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_associator_law dα) : disp_associator_nat_leftwhisker dα := pr1 dαl.
  Definition disp_associatorlaw_natright {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_associator_law dα) : disp_associator_nat_rightwhisker dα := pr1(pr2 dαl).
  Definition disp_associatorlaw_natleftright {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_associator_law dα) : disp_associator_nat_leftrightwhisker dα := pr1 (pr2 (pr2 dαl)).
  Definition disp_associatorlaw_iso {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_associator_law dα) : disp_associator_iso dα := pr2 (pr2 (pr2 dαl)).

  (* Definition is_dispnatiso {C D : category} {CC: disp_cat C} {DD : disp_cat D} {F G : functor C D} {α : nat_trans F G} (αiso : is_nat_z_iso α) { FF : disp_functor F CC DD } {GG : disp_functor G CC DD} (αα : disp_nat_trans α FF GG) : UU                                                    := ∏ (x : C) (xx : CC x), is_z_iso_disp (α x,,αiso x) (αα x xx). *)

  Definition disp_leftunitor_nat {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor_data DT i) : UU :=
    ∏ (x y : C) (f : C⟦x,y⟧) (xx : D x) (yy : D y) (ff : xx -->[f] yy), (i ⊗⊗^{DT}_{l} ff) ;; (dlu y yy) = transportb _ (pr1 (monoidal_leftunitorlaw M) _ _ _) (dlu x xx ;; ff).

  Definition disp_leftunitor_iso {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor_data DT i) : UU :=
    ∏ (x : C) (xx : D x), is_z_iso_disp (lu^{M}_{x},,pr2 (monoidal_leftunitorlaw M) x) (dlu x xx).

  Definition disp_leftunitor_law {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor_data DT i) : UU :=
    disp_leftunitor_nat dlu × disp_leftunitor_iso dlu.

  Definition disp_rightunitor_nat {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dru : disp_rightunitor_data DT i) : UU :=
    ∏ (x y : C) (f : C⟦x,y⟧) (xx : D x) (yy : D y) (ff : xx -->[f] yy), (ff ⊗⊗^{DT}_{r} i) ;; (dru y yy) = transportb _ (pr1 (monoidal_rightunitorlaw M) _ _ _) (dru x xx ;; ff).

  Definition disp_rightunitor_iso {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dru : disp_rightunitor_data DT i) : UU :=
    ∏ (x : C) (xx : D x), is_z_iso_disp (ru^{M}_{x},,pr2 (monoidal_rightunitorlaw M) x) (dru x xx).

  Definition disp_rightunitor_law {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dru : disp_rightunitor_data DT i) : UU :=
    disp_rightunitor_nat dru × disp_rightunitor_iso dru.

  Definition disp_triangle_identity {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor_data DT i) (dru : disp_rightunitor_data DT i) (dα : disp_associator_data DT) : UU
    := ∏ (x y : C), ∏ (xx : D x) (yy : D y), ((dα x I_{M} y xx i yy) ;; (xx ⊗⊗^{DT}_{l} dlu y yy )) = transportb _ ((monoidal_triangleidentity M) x y) ((dru x xx) ⊗⊗^{DT}_{r} yy).

  Definition disp_pentagon_identity {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
    := ∏ (w x y z : C), ∏ (ww : D w) (xx : D x) (yy : D y) (zz : D z),
      ((dα _ _ _ ww xx yy) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ ww (xx ⊗⊗_{DT} yy) zz) ;; (ww ⊗⊗^{DT}_{l} (dα _ _ _ xx yy zz)) =
        transportb _ ((monoidal_pentagonidentity M) w x y z) ((dα _ _ _ (ww ⊗⊗_{DT} xx) yy zz) ;; (dα _ _ _ ww xx (yy ⊗⊗_{DT} zz))).

  Definition disp_monoidal_laws {C : category} {D : disp_cat C} {M : monoidal C} (DMD :  disp_monoidal_data D M) : UU :=
   (disp_associator_law dα_{DMD}) × (disp_leftunitor_law dlu_{DMD}) × (disp_rightunitor_law dru_{DMD})
                       × (disp_triangle_identity dlu_{DMD} dru_{DMD} dα_{DMD}) × (disp_pentagon_identity dα_{DMD}).

  Definition disp_monoidal {C : category} (D : disp_cat C) (M : monoidal C) : UU :=
  ∑ (MD : disp_monoidal_data D M), (disp_monoidal_laws MD).

  Definition disp_monoidal_mondata {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_monoidal_data D M := pr1 DM.
  Coercion disp_monoidal_mondata : disp_monoidal >-> disp_monoidal_data.

  Definition disp_monoidal_monlaws {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_monoidal_laws DM := pr2 DM.
  Definition disp_monoidal_associatorlaw {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_associator_law dα_{DM} := pr1 (disp_monoidal_monlaws DM).
  Definition disp_monoidal_leftunitorlaw  {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_leftunitor_law dlu_{DM} := pr1 (pr2 (disp_monoidal_monlaws DM)).
  Definition disp_monoidal_rightunitorlaw  {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_rightunitor_law dru_{DM} := pr1 (pr2 (pr2 (disp_monoidal_monlaws DM))).
  Definition disp_monoidal_triangleidentity  {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_triangle_identity dlu_{DM} dru_{DM} dα_{DM} := pr1 (pr2 (pr2 (pr2 (disp_monoidal_monlaws DM)))).
  Definition disp_monoidal_pentagonidentity  {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : disp_pentagon_identity dα_{DM} := pr2 (pr2 (pr2 (pr2 (disp_monoidal_monlaws DM)))).

End DisplayedMonoidalCategories.

Module DisplayedMonoidalNotations.
  Notation "dI_{ M }" := (disp_monoidal_unit M).
  Notation "dlu^{ M }" := (disp_monoidal_leftunitor M).
  Notation "dru^{ M }" := (disp_monoidal_rightunitor M).
  Notation "dα^{ M }" := (disp_monoidal_associator M).
  Notation "dlu^{ M }_{ x }" := (disp_monoidal_leftunitor M x).
  Notation "dru^{ M }_{ x }" := (disp_monoidal_rightunitor M x).
  Notation "dα^{ M }_{ x , y , z }" := (disp_monoidal_associator M x y z).
End DisplayedMonoidalNotations.
