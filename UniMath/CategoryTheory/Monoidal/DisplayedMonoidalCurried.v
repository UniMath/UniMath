(* In this file we formalize the definition of a certain monoidal structure on a display category and show that the total category has the structure of a monoidal category if the base category is a monoidal category and the displayed category has this certain monoidal structure.

The data of a displayed monoidal category consists of:
    - A (base) category C.
    - A displayed category D over C.
    - A displayed tensor DT which consists of:
                  - D_x → D_y → D_{x ⊗_{T} y} : a → (b → a⊗_{{DT}} b).
                  - (a -->[f] a') → (b -->[g] b') → ( (a ⊗_{{DT}} b) -->[f ⊗^{T} g] (a' ⊗_{{DT}} b') : f'→g'→ (f' ⊗^{{DT}} g').
    - A term i : D I, called the displayed unit.
    - A natural transformation dlu : (i ⊗_{{TD}} (-)) -->[lu_x] (-) with naturality condition:
                  - (id_i ⊗^{{TD}} f') ;; dlu_b = dlu_a ;; f'
                  where the equality is dependent over the naturality condition of lu w.r.t. f, i.e. we have to transport.
    - A natural transformation dru : ((-) ⊗_{{TD}} i) -->[ru_x] (-) with naturality condition:
                  - (f' ⊗^{{TD}} id_i) ;; dru_b = dru_a ;; f'
                  where the equality is dependent over the naturality condition of ru w.r.t. f, i.e. we have to transport.
    - A natural transformation dα : ((-)⊗(-))⊗(-) -->[α_{x,y,z}] (-)⊗((-)⊗(-)) with naturality condition:
                  - dα_{a,b,c} ;; (f' ⊗^{{TD}} (g' ⊗^{{TD}} h')) = (f'⊗g')⊗h' ;; dα_{a',b',c'}
And the properties of a displayed monoidal category are given by:
    - Displayed triangle identity:
                  - dα_{a,i,b} ;; (id_a ⊗ dlu_b) = dru_a ⊗ id_b.
    - Displayed pentagon_identity:
                  -

*)


Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section displayedmonoidalcategories.

  Context (C : category) (D : disp_cat C) (T : tensor_data C) (I : C) (α : associator_data T) (lu : leftunitor_data T I) (ru : rightunitor_data T I) (tid : tensorfunctor_id T) (tcomp : tensorfunctor_comp T) (αnat : associator_naturality α) (αiso : associator_is_natiso α) (lunat : leftunitor_naturality lu) (luiso : leftunitor_is_natiso lu) (runat : rightunitor_naturality ru) (ruiso : rightunitor_is_natiso ru) (tri : triangle_identity lu ru α) (pen : pentagon_identity α).

  Definition displayedtensor_data : UU :=
    ∑ (dt : ∏ (x y : C), (D x) → (D y) -> (D (x ⊗_{T} y))),
    ∏ (x x' y y' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y'),
      (a -->[f] a') -> (b -->[g] b') -> ((dt x y a b)-->[f ⊗^{T} g] (dt x' y' a' b')).

  Definition displayedtensoronobjects_from_displayedtensordata (dtd : displayedtensor_data)
    :  ∏ (x y : C), (D x) → (D y) -> (D (x ⊗_{T} y)) := pr1 dtd.
  Notation "a ⊗_{{ dtd }} b" := (displayedtensoronobjects_from_displayedtensordata dtd _ _ a b) (at level 31).

  Definition displayedtensoronmorphisms_from_displayedtensordata (dtd : displayedtensor_data) :
    ∏ (x x' y y' : C) (f : C ⟦ x, x' ⟧) (g : C ⟦ y, y' ⟧) (a : D x) (a' : D x') (b : D y) (b' : D y'),
  (a -->[ f] a') -> (b -->[ g] b') -> ((a ⊗_{{dtd}} b) -->[ f ⊗^{ T} g ] (a' ⊗_{{ dtd}} b'))
    := pr2 dtd.
  Notation "f' ⊗^{{ dtd }} g'" := (displayedtensoronmorphisms_from_displayedtensordata dtd _ _ _ _ _ _ _ _ _ _ f' g'  ) (at level 31).

  Definition displayedassociator_data (dtd : displayedtensor_data) : UU :=
    ∏ (x y z : C), ∏ (a : D x) (b : D y) (c : D z),
      ((a ⊗_{{dtd}} b) ⊗_{{dtd}} c) -->[(α x y z)] (a ⊗_{{dtd}} (b ⊗_{{dtd}} c)).

  Definition displayedleftunitor_data (dtd : displayedtensor_data) (i : D I) : UU
    := ∏ (x : C), ∏ (a : D x), ((i ⊗_{{dtd}} a)-->[(lu x)] a).

  Definition displayedrightunitor_data (dtd : displayedtensor_data) (i : D I) : UU
    := ∏ (x : C), ∏ (a : D x), ((a ⊗_{{dtd}} i)-->[(ru x)] a).

  Definition displayedmonoidalcat_data : UU :=
    ∑ dtd : displayedtensor_data, ∑ i : D I,
          (displayedleftunitor_data dtd i) × (displayedrightunitor_data dtd i) × (displayedassociator_data dtd).

  Definition displayedtensordata_from_dispmoncatdata (DMD : displayedmonoidalcat_data) : displayedtensor_data := pr1 DMD.
  Coercion displayedtensordata_from_dispmoncatdata : displayedmonoidalcat_data >-> displayedtensor_data.

  Definition displayedunit_from_dispmoncatdata (DMD : displayedmonoidalcat_data) : D I := pr1 (pr2 DMD).
  Coercion displayedunit_from_dispmoncatdata : displayedmonoidalcat_data >-> ob_disp.

  Definition displayedleftunitordata_from_dispmoncatdata (DMD : displayedmonoidalcat_data) : displayedleftunitor_data DMD DMD := pr1 (pr2 (pr2 DMD)).
  Coercion displayedleftunitordata_from_dispmoncatdata : displayedmonoidalcat_data >-> displayedleftunitor_data.

  Definition displayedrightunitordata_from_dispmoncatdata (DMD : displayedmonoidalcat_data) : displayedrightunitor_data DMD DMD := pr1 (pr2 (pr2 (pr2 DMD))).
  Coercion displayedrightunitordata_from_dispmoncatdata : displayedmonoidalcat_data >-> displayedrightunitor_data.

  Definition displayedassociatordata_from_dispmoncatdata (DMD : displayedmonoidalcat_data) : displayedassociator_data DMD := pr2 (pr2 (pr2 (pr2 DMD))).
  Coercion displayedassociatordata_from_dispmoncatdata : displayedmonoidalcat_data >-> displayedassociator_data.


  (** PROPERTIES **)
  Definition displayedtensor_id (dtd : displayedtensor_data)
    := ∏ (x y : C), ∏ (a : D x) (b : D y),  ((id_disp a) ⊗^{{dtd}} (id_disp b))  = transportb _ (tid x y) (id_disp (a ⊗_{{dtd}} b)).

  Definition displayedtensor_comp (dtd : displayedtensor_data)
    := ∏ (x y x' y' x'' y'': C), ∏ (a : D x) (b : D y) (a' : D x') (b' : D y') (a'' : D x'') (b'' : D y''),
      ∏ (f1 : C⟦x, x'⟧) (g1 : C⟦y,y'⟧) (f2 : C⟦x',x''⟧) (g2 : C⟦y',y''⟧) (f1' : a -->[f1] a') (g1' : b -->[g1] b') (f2' : a' -->[f2] a'') (g2' : b' -->[g2] b''), ((f1'⊗^{{dtd}} g1') ;; (f2'⊗^{{dtd}} g2')) = transportb _ (tcomp x y x' y' x'' y'' f1 f2 g1 g2) ((f1';;f2') ⊗^{{dtd}} (g1';;g2')).

  Definition displayedassociator_naturality {dtd : displayedtensor_data} (dα : displayedassociator_data dtd) : UU :=
    ∏ (x x' y y' z z' : C), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y') (c : D z) (c' : D z'),
      ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧), ∏ (f' : a-->[f] a') (g' : b -->[g] b') (h' : c -->[h] c'),
      ((dα x y z a b c) ;; (f' ⊗^{{dtd}} (g' ⊗^{{dtd}} h'))) = transportb _ (αnat _ _ _ _ _ _ f g h) (((f' ⊗^{{dtd}} g') ⊗^{{dtd}} h') ;; dα _ _ _ a' b' c').

  Definition displayedassociator_is_nat_iso {dtd : displayedtensor_data} (dα : displayedassociator_data dtd) : UU :=
    ∏ (x y z : C), ∏ (a : D x) (b : D y) (c : D z), is_iso_disp (z_iso_to_iso ((α x y z),,(αiso x y z))) (dα x y z a b c).

  Definition displayedleftunitor_naturality {i : D I} {dtd : displayedtensor_data} (dlud : displayedleftunitor_data dtd i) : UU :=
    ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b),
      (dlud x a) ;; f' = transportb _ (lunat x y f) (((id_disp i) ⊗^{{dtd}} f') ;; (dlud y b)).

  Definition displayedleftunitor_is_nat_iso {i : D I} {dtd : displayedtensor_data} (dlu : displayedleftunitor_data dtd i) : UU :=
    ∏ (x : C), ∏ (a : D x), is_iso_disp (z_iso_to_iso (lu x,, luiso x)) (dlu x a).

  Definition displayedrightunitor_naturality {dtd : displayedtensor_data} {i : D I} (drud : displayedrightunitor_data dtd i) : UU :=
    ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b),
      ((drud x a) ;; f') = transportb _ (runat x y f) (( f' ⊗^{{dtd}}  (id_disp i)) ;; (drud y b)).

  Definition displayedrightunitor_is_nat_iso {i : D I} {dtd : displayedtensor_data} (dru : displayedrightunitor_data dtd i) : UU :=
    ∏ (x : C), ∏ (a : D x), is_iso_disp (z_iso_to_iso (ru x,, ruiso x)) (dru x a).

  Definition displayedtriangle_identity {dtd : displayedtensor_data} {i : D I} (dlud : displayedleftunitor_data dtd i) (drud : displayedrightunitor_data dtd i) (dα : displayedassociator_data dtd) := ∏ (x y : C), ∏ (a : D x) (b : D y),
      ((dα x I y a i b) ;; ((id_disp a)  ⊗^{{dtd}} dlud y b )) = transportb _ (tri x y) ((drud x a) ⊗^{{dtd}} id_disp b).

  Definition displayedpentagon_identity {dtd : displayedtensor_data} (dα : displayedassociator_data dtd) : UU
    := ∏ (w x y z: C), ∏ (e : D w) (a : D x) (b : D y) (c : D z),
      (((dα _ _ _ e a b) ⊗^{{dtd}} (id_disp c)) ;; (dα _ _ _ e (a ⊗_{{dtd}} b) c) ;; ((id_disp e) ⊗^{{dtd}}  (dα _ _ _  a b c))) = transportb _ (pen w x y z) ((dα (w ⊗_{T} x) y z (e ⊗_{{dtd}} a) b c) ;; (dα w x (y ⊗_{T} z) e a (b ⊗_{{dtd}} c))).

  Definition displayedmonoidal_laws (DMD :  displayedmonoidalcat_data) : UU :=
    (displayedtensor_id DMD) × (displayedtensor_comp DMD) ×
                             (displayedassociator_naturality DMD) × (displayedassociator_is_nat_iso DMD) ×
                             (displayedleftunitor_naturality DMD) × (displayedleftunitor_is_nat_iso DMD) ×
                             (displayedrightunitor_naturality DMD) × (displayedrightunitor_is_nat_iso DMD) ×
                             (displayedtriangle_identity DMD DMD DMD) × (displayedpentagon_identity DMD).

  Definition displayedtensorid_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedtensor_id DMD := pr1 DML.
Coercion displayedtensorid_from_monoidallaws : displayedmonoidal_laws >-> displayedtensor_id.

Definition displayedtensorcomp_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedtensor_comp DMD := pr1 (pr2 DML).
Coercion displayedtensorcomp_from_monoidallaws : displayedmonoidal_laws >-> displayedtensor_comp.

Definition displayedassociatornaturality_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedassociator_naturality DMD := pr1 (pr2 (pr2 DML)).
Coercion displayedassociatornaturality_from_monoidallaws : displayedmonoidal_laws >-> displayedassociator_naturality.

Definition displayedassociatorisiso_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedassociator_is_nat_iso DMD := pr1 (pr2 (pr2 (pr2 DML))).
Coercion displayedassociatorisiso_from_monoidallaws : displayedmonoidal_laws >-> displayedassociator_is_nat_iso.

Definition displayedleftunitornaturality_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedleftunitor_naturality DMD := pr1 (pr2 (pr2 (pr2 (pr2 DML)))).
Coercion displayedleftunitornaturality_from_monoidallaws : displayedmonoidal_laws >-> displayedleftunitor_naturality.

Definition displayedleftunitorisiso_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedleftunitor_is_nat_iso DMD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DML))))).
Coercion displayedleftunitorisiso_from_monoidallaws : displayedmonoidal_laws >-> displayedleftunitor_is_nat_iso.

Definition displayedrightunitornaturality_from_monoidallaws{DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedrightunitor_naturality DMD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DML)))))).
Coercion displayedrightunitornaturality_from_monoidallaws : displayedmonoidal_laws >-> displayedrightunitor_naturality.

Definition displayedrightunitorisiso_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedrightunitor_is_nat_iso DMD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DML))))))).
Coercion displayedrightunitorisiso_from_monoidallaws : displayedmonoidal_laws >-> displayedrightunitor_is_nat_iso.

Definition displayedtriangleidentity_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedtriangle_identity DMD DMD DMD := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DML)))))))).
Coercion displayedtriangleidentity_from_monoidallaws : displayedmonoidal_laws >-> displayedtriangle_identity.

Definition displayedpentagonidentity_from_monoidallaws {DMD : displayedmonoidalcat_data} (DML : displayedmonoidal_laws DMD) : displayedpentagon_identity DMD := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DML)))))))).
Coercion displayedpentagonidentity_from_monoidallaws : displayedmonoidal_laws >-> displayedpentagon_identity.

End displayedmonoidalcategories.
