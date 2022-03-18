Require Import UniMath.Foundations.All.
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

Import Notations.
Import DisplayedBifunctorNotations.

Section DisplayedMonoidalCategories.

  Local Notation "I_{ M }" := (unit_from_monoidalcatdata M).
  Local Notation "lu^{ M }" := (leftunitor_from_monoidalcatdata M).
  Local Notation "ru^{ M }" := (rightunitor_from_monoidalcatdata M).
  Local Notation "α^{ M }" := (associatordata_from_monoidalcatdata M).
  Local Notation "lu^{ M }_{ x }" := ( (leftunitor_from_monoidalcatdata M) x ).
  Local Notation "ru^{ M }_{ x }" := ( (rightunitor_from_monoidalcatdata M) x ).
  Local Notation "α^{ M }_{ x , y , z }" := (associatordata_from_monoidalcatdata M x y z).

  Definition disp_tensor {C : category} (D : disp_cat C) (M : monoidalcategory C) : UU := disp_bifunctor M D D D.
  Identity Coercion disptensor_into_dispbifunctor : disp_tensor >-> disp_bifunctor.

  Definition disp_associator_data {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : UU :=
    ∏ (x y z : C), ∏ (xx : D x) (yy : D y) (zz : D z),
      ((xx ⊗⊗_{DT} yy) ⊗⊗_{DT} zz) -->[α^{M}_{x,y,z}] (xx ⊗⊗_{DT} (yy ⊗⊗_{DT} zz)).

  Definition disp_leftunitor {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) (i : D I_{M}) : UU :=
    disp_nat_trans lu^{M} (leftwhiskering_dispfunctor DT (disp_bifunctor_leftid DT) (disp_bifunctor_leftcomp DT) I_{M} i) (disp_functor_identity D).
  Identity Coercion displeftunitorintonattrans : disp_leftunitor >-> disp_nat_trans.

  Definition disp_rightunitor {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) (i : D I_{M}) : UU :=
    disp_nat_trans ru^{M} (rightwhiskering_dispfunctor DT (disp_bifunctor_rightid DT) (disp_bifunctor_rightcomp DT) I_{M} i) (disp_functor_identity D).
  Identity Coercion disprightunitorintonattrans : disp_rightunitor >-> disp_nat_trans.


  Definition disp_monoidalcat_data {C : category} (D : disp_cat C) (M : monoidalcategory C) : UU :=
    ∑ DT : disp_tensor D M, ∑ i : D I_{M},
          (disp_leftunitor DT i) × (disp_rightunitor DT i) × (disp_associator_data DT).

  Definition disp_tensor_from_dispmoncatdata {C : category} {D : disp_cat C} {M : monoidalcategory C} (DMD : disp_monoidalcat_data D M) : disp_tensor D M := pr1 DMD.
  Coercion disp_tensor_from_dispmoncatdata : disp_monoidalcat_data >-> disp_tensor.

  Definition disp_unit_from_dispmoncatdata {C : category} {D : disp_cat C} {M : monoidalcategory C} (DMD : disp_monoidalcat_data D M) : D I_{M} := pr1 (pr2 DMD).
  Coercion disp_unit_from_dispmoncatdata : disp_monoidalcat_data >-> ob_disp.

  Definition disp_leftunitor_from_dispmoncatdata {C : category} {D : disp_cat C} {M : monoidalcategory C} (DMD : disp_monoidalcat_data D M) : disp_leftunitor DMD DMD := pr1 (pr2 (pr2 DMD)).
  Coercion disp_leftunitor_from_dispmoncatdata : disp_monoidalcat_data >-> disp_leftunitor.

  Definition disp_rightunitor_from_dispmoncatdata {C : category} {D : disp_cat C} {M : monoidalcategory C} (DMD : disp_monoidalcat_data D M) : disp_rightunitor DMD DMD := pr1 (pr2 (pr2 (pr2 DMD))).
  Coercion disp_rightunitor_from_dispmoncatdata : disp_monoidalcat_data >-> disp_rightunitor.

  Definition disp_associatordata_from_dispmoncatdata {C : category} {D : disp_cat C} {M : monoidalcategory C} (DMD : disp_monoidalcat_data D M) : disp_associator_data DMD := pr2 (pr2 (pr2 (pr2 DMD))).
  Coercion disp_associatordata_from_dispmoncatdata : disp_monoidalcat_data >-> disp_associator_data.

  (** PROPERTIES **)
  Definition disp_tensor_assoc_nat_leftwhisker {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
  := ∏ (x y z1 z2 : C) (h : C⟦z1,z2⟧) (xx : D x) (yy : D y) (zz1 : D z1) (zz2 : D z2) (hh : zz1-->[h] zz2),
      (dα _ _ _ xx yy zz1) ;; (xx ⊗⊗^{DT}_{l} (yy ⊗⊗^{DT}_{l} hh)) = transportb _ (pr1 (moncat_associator M) x y z1 z2 h) (((xx ⊗⊗_{DT} yy) ⊗⊗^{DT}_{l} hh) ;; (dα _ _ _ xx yy zz2)).

  Definition disp_tensor_assoc_nat_rightwhisker {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
  := ∏ (x1 x2 y z : C) (f : C⟦x1,x2⟧) (xx1 : D x1) (xx2 : D x2) (yy : D y) (zz : D z) (ff : xx1-->[f] xx2),
    (dα _ _ _ xx1 yy zz) ;; (ff ⊗⊗^{DT}_{r} (yy ⊗⊗_{DT} zz)) = transportb _ (pr1 (pr2 (moncat_associator M)) x1 x2 y z f) (((ff ⊗⊗^{DT}_{r} yy) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ xx2 yy zz)).

  Definition disp_tensor_assoc_nat_leftrightwhisker {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
  := ∏ (x y1 y2 z : C) (g : C⟦y1,y2⟧) (xx : D x) (yy1 : D y1) (yy2 : D y2) (zz : D z) (gg : yy1-->[g] yy2),
      (dα _ _ _ xx yy1 zz) ;; (xx ⊗⊗^{DT}_{l} (gg ⊗⊗^{DT}_{r} zz)) = transportb _ (pr1 (pr2 (pr2 (moncat_associator M))) x y1 y2 z g) (((xx ⊗⊗^{DT}_{l} gg) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ xx yy2 zz)).

  Definition displayedassociator_naturality {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dtl :  disp_tensor_assoc_nat_leftwhisker dα) (dtr : disp_tensor_assoc_nat_rightwhisker dα) (dtlr : disp_tensor_assoc_nat_leftrightwhisker dα) :
    ∏ (x1 x2 y1 y2 z1 z2 : C), ∏ (xx1 : D x1) (xx2 : D x2) (yy1 : D y1) (yy2 : D y2) (zz1 : D z1) (zz2 : D z2),
      ∏ (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧) (h : C⟦z1,z2⟧), ∏ (ff : xx1-->[f] xx2) (gg : yy1 -->[g] yy2) (hh : zz1 -->[h] zz2),
      ((dα _ _ _ xx1 yy1 zz1) ;; (ff ⊗⊗^{DT} (gg ⊗⊗^{DT} hh))) = transportb _ (tensor_assoc_nat2 (pr1 (moncat_associator M)) (pr1 (pr2 (moncat_associator M))) (pr1 (pr2 (pr2 (moncat_associator M)))) f g h) (((ff ⊗⊗^{DT} gg) ⊗⊗^{DT} hh) ;; dα _ _ _ xx2 yy2 zz2).
  Proof.
    intros.
    unfold dispfunctoronmorphisms1.
  Admitted.

  Definition disp_tensor_assoc_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU :=
    ∏ (x y z : C), ∏ (xx : D x) (yy : D y) (zz : D z), is_z_iso_disp
        ((α^{M}_{x,y,z}),,(tensorassociator_iso (moncat_associator M) x y z)) (dα _ _ _ xx yy zz).

  Definition disp_assoc_law  {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU :=
  (disp_tensor_assoc_nat_leftwhisker dα) × (disp_tensor_assoc_nat_rightwhisker dα) × (disp_tensor_assoc_nat_leftrightwhisker dα) × (disp_tensor_assoc_iso dα).

  Definition disp_tensorassoc_natleft {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_assoc_law dα) : disp_tensor_assoc_nat_leftwhisker dα := pr1 dαl.
  Definition disp_tensorassoc_natright {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_assoc_law dα) : disp_tensor_assoc_nat_rightwhisker dα := pr1(pr2 dαl).
  Definition disp_tensorassoc_natleftright {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_assoc_law dα) : disp_tensor_assoc_nat_leftrightwhisker dα := pr1 (pr2 (pr2 dαl)).
  Definition disp_tensorassoc_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {dα : disp_associator_data DT} (dαl : disp_assoc_law dα) : disp_tensor_assoc_iso dα := pr2 (pr2 (pr2 dαl)).

  Definition is_dispnatiso {C D : category} {CC: disp_cat C} {DD : disp_cat D} {F G : functor C D} {α : nat_trans F G} (αiso : is_nat_z_iso α) { FF : disp_functor F CC DD } {GG : disp_functor G CC DD} (αα : disp_nat_trans α FF GG) : UU                                                    := ∏ (x : C) (xx : CC x), is_z_iso_disp (α x,,αiso x) (αα x xx).

  Definition disp_leftunitor_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) (i : D I_{M}) (dlu : disp_leftunitor DT i) : UU := is_dispnatiso (moncat_leftunitoriso M) dlu.

  Definition disp_rightunitor_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) (i : D I_{M}) (dru : disp_rightunitor DT i) : UU := is_dispnatiso (moncat_rightunitoriso M) dru.

  Definition disp_triangle_identity {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor DT i) (dru : disp_rightunitor DT i) (dα : disp_associator_data DT) : UU
    := ∏ (x y : C), ∏ (xx : D x) (yy : D y), ((dα x I_{M} y xx i yy) ;; (xx ⊗⊗^{DT}_{l} dlu y yy )) = transportb _ ((moncat_triangleidentity M) x y) ((dru x xx) ⊗⊗^{DT}_{r} yy).

  Definition disp_pentagon_identity {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : UU
    := ∏ (w x y z : C), ∏ (ww : D w) (xx : D x) (yy : D y) (zz : D z),
      ((dα _ _ _ ww xx yy) ⊗⊗^{DT}_{r} zz) ;; (dα _ _ _ ww (xx ⊗⊗_{DT} yy) zz) ;; (ww ⊗⊗^{DT}_{l} (dα _ _ _ xx yy zz)) =
        transportb _ ((moncat_pentagonidentity M) w x y z) ((dα _ _ _ (ww ⊗⊗_{DT} xx) yy zz) ;; (dα _ _ _ ww xx (yy ⊗⊗_{DT} zz))).

  Definition disp_monoidal_laws {C : category} {D : disp_cat C} {M : monoidalcategory C} (DMD :  disp_monoidalcat_data D M) : UU :=
   (disp_assoc_law DMD) × (disp_leftunitor_iso DMD DMD DMD) × (disp_rightunitor_iso DMD DMD DMD)
                       × (disp_triangle_identity DMD DMD DMD) × (disp_pentagon_identity DMD).

  Definition disp_monoidalcategory {C : category} (D : disp_cat C) (M : monoidalcategory C) : UU :=
  ∑ (MD : disp_monoidalcat_data D M), (disp_monoidal_laws MD).

  Definition dispmonoidalcatdata_from_dispmoncat {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_monoidalcat_data D M := pr1 DM.
  Coercion dispmonoidalcatdata_from_dispmoncat : disp_monoidalcategory >-> disp_monoidalcat_data.

  Definition dispmonoidallaws_from_dispmoncat {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_monoidal_laws DM := pr2 DM.
  Definition disp_moncat_associator {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_assoc_law DM := pr1 (dispmonoidallaws_from_dispmoncat DM).
  Definition disp_moncat_leftunitoriso  {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_leftunitor_iso DM DM DM := pr1 (pr2 (dispmonoidallaws_from_dispmoncat DM)).
  Definition disp_moncat_rightunitoriso  {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_rightunitor_iso DM DM DM := pr1 (pr2 (pr2 (dispmonoidallaws_from_dispmoncat DM))).
  Definition disp_moncat_triangleidentity  {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_triangle_identity DM DM DM := pr1 (pr2 (pr2 (pr2 (dispmonoidallaws_from_dispmoncat DM)))).
  Definition disp_moncat_pentagonidentity  {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : disp_pentagon_identity DM := pr2 (pr2 (pr2 (pr2 (dispmonoidallaws_from_dispmoncat DM)))).

End DisplayedMonoidalCategories.
