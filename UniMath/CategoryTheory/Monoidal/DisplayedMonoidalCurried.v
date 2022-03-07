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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


  Definition displayed_tensor {C : category} (T : tensor C) (D : disp_cat C) : UU :=
    ∑ (tensor_ob : ∏ (x y : C), (D x) → (D y) -> (D (x ⊗_{T} y))),
    ∏ (x x' y y' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y'),
      (a -->[f] a') -> (b -->[g] b') -> ((tensor_ob x y a b)-->[f ⊗^{T} g] (tensor_ob x' y' a' b')).

  Definition displayed_tensor_data : UU :=
    ∑ (C : category), ∑ (T : tensor C), ∑ (D : disp_cat C), displayed_tensor T D.

  Definition cat_from_displayedtensor_data (dtd : displayed_tensor_data) : category := pr1 dtd.
  Coercion cat_from_displayedtensor_data : displayed_tensor_data >-> category.

  Definition tensor_from_displayedtensor_data (dtd : displayed_tensor_data) : tensor dtd := pr1 (pr2 dtd).
  Coercion tensor_from_displayedtensor_data : displayed_tensor_data >-> tensor.

  Definition dispcat_from_displayedtensor_data (dtd : displayed_tensor_data) : disp_cat dtd := pr1 (pr2 (pr2 dtd)).
  Coercion dispcat_from_displayedtensor_data : displayed_tensor_data >-> disp_cat.

  Definition disptensor_from_displayedtensor_data (dtd : displayed_tensor_data) : displayed_tensor dtd dtd := pr2 (pr2 (pr2 dtd)).
  Coercion disptensor_from_displayedtensor_data : displayed_tensor_data >-> displayed_tensor.

  Definition displayedtensor_on_objects_from_displayedtensor_data {C : category} {T : tensor C} {D : disp_cat C} (dtd : displayed_tensor T D)  : ∏ (x y : C), (D x) → (D y) -> (D (x ⊗_{T} y)) := pr1 dtd.
  Notation "a ⊗_{{ dtd }} b" := (displayedtensor_on_objects_from_displayedtensor_data dtd _ _ a b) (at level 31).

  Definition displayedtensor_on_morphisms_from_displayedtensor_data {C : category} {T : tensor C} {D : disp_cat C} (dtd : displayed_tensor T D) : ∏ (x x' y y' : C) (f : C ⟦ x, x' ⟧) (g : C ⟦ y, y' ⟧) (a : D x) (a' : D x') (b : D y) (b' : D y'),
  (a -->[ f] a') -> (b -->[ g] b') -> ((a ⊗_{{dtd}} b) -->[ f ⊗^{ T} g ] (a' ⊗_{{ dtd}} b'))
    := pr2 dtd.
  Notation "f' ⊗^{{ dtd }} g'" := (displayedtensor_on_morphisms_from_displayedtensor_data dtd _ _ _ _ _ _ _ _ _ _ f' g'  ) (at level 31).


  (* Remark::A unit for a displayed category D consists of the unit in C and a term in (D I), hence we do not need any special construction right now *)

  Definition displayed_leftunitor_on_objects {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (lu : left_unitor_on_objects T I) : UU :=
    ∏ (x : C), ∏ (a : D x), ((i ⊗_{{TD}} a)-->[(lu x)] a).

  Definition displayed_leftunitor_naturality {C : category} {T : tensor C} {I : C} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {lu : left_unitor T I} (dlu : displayed_leftunitor_on_objects TD i (pr1 lu)) : UU :=
    ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b), (((id_disp i) ⊗^{{TD}} f') ;; (dlu y b)) = transportb _ ((pr2 lu) x y f) ((dlu x a) ;; f').

(* TEST *)
(*
Definition ayed_leftunitor_naturality {C : category} {T : tensor C} {I : C} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {lu : left_unitor T I} (dlu : displayed_leftunitor_on_objects TD i (pr1 lu)) : ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b), nat.
Proof.
  intros x y a b f f'.
  Check (((id_disp i) ⊗^{{TD}} f') ;; (dlu y b)).
  Check (dlu x a) ;; f'.
  = transportb _ ((pr2 lu) x y f) ((dlu x a) ;; f').
  *)

  Definition displayed_leftunitor {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (lu : left_unitor T I) : UU :=
    ∑ (dlu : displayed_leftunitor_on_objects TD i (pr1 lu)), displayed_leftunitor_naturality dlu.

  Definition displayed_rightunitor_on_objects {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (ru : right_unitor_on_objects T I) : UU :=
    ∏ (x : C), ∏ (a : D x), ((a ⊗_{{TD}} i)-->[(ru x)] a).

  Definition displayed_rightunitor_naturality {C : category} {T : tensor C} {I : C} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {ru : right_unitor T I} (dru : displayed_rightunitor_on_objects TD i (pr1 ru)) : UU :=
    ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b),
      (( f' ⊗^{{TD}}  (id_disp i)) ;; (dru y b)) = transportb _ ((pr2 ru) x y f)   ((dru x a) ;; f').

  Definition displayed_rightunitor {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (ru : right_unitor T I) : UU :=
    ∑ (dru : displayed_rightunitor_on_objects TD i (pr1 ru)), displayed_rightunitor_naturality dru.

  Definition displayed_associator_on_objects {C : category} {T : tensor C} {D : disp_cat C} (TD : displayed_tensor T D) (α : associator_on_objects T) : UU :=
    ∏ (x y z : C), ∏ (a : D x) (b : D y) (c : D z),
      ((a ⊗_{{TD}} b) ⊗_{{TD}} c) -->[(α x y z)] (a ⊗_{{TD}} (b ⊗_{{TD}} c)).

  Definition displayed_associator_naturality {C : category} {T : tensor C} {D : disp_cat C} {TD : displayed_tensor T D} {α : associator T} (dα : displayed_associator_on_objects TD (pr1 α)) : UU :=
    ∏ (x x' y y' z z' : C), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y') (c : D z) (c' : D z'),
      ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧), ∏ (f' : a-->[f] a') (g' : b -->[g] b') (h' : c -->[h] c'), (dα x y z a b c) ;; (f' ⊗^{{TD}} (g' ⊗^{{TD}} h')) =  transportb _ ((pr2 α) _ _ _ _ _ _ f g h) ( ((f' ⊗^{{TD}} g') ⊗^{{TD}} h') ;; dα _ _ _ a' b' c' ).

  Definition displayed_associator {C : category} {T : tensor C} (α : associator T) {D : disp_cat C} (TD : displayed_tensor T D) : UU :=
    ∑ (dα_ob : displayed_associator_on_objects TD (pr1 α)), (displayed_associator_naturality dα_ob).

Definition displayed_tensor_functoriality_id {C : category} {T : tensor C} (pfTensorId : tensor_functor_id T) {D : disp_cat C} (TD : displayed_tensor T D) := ∏ (x y : C), ∏ (a : D x) (b : D y), (transportf _ (pfTensorId x y) ((id_disp a) ⊗^{{TD}} (id_disp b)))  = (id_disp (a ⊗_{{TD}} b)).

Definition displayed_tensor_functoriality_comp {C : category} {T : tensor C} (pfTensorComp : tensor_functor_comp T) {D : disp_cat C} (TD : displayed_tensor T D) := ∏ (x y x' y' x'' y'': C), ∏ (a : D x) (b : D y) (a' : D x') (b' : D y') (a'' : D x'') (b'' : D y''),
    ∏ (f1 : C⟦x, x'⟧) (g1 : C⟦y,y'⟧) (f2 : C⟦x',x''⟧) (g2 : C⟦y',y''⟧) (f1' : a -->[f1] a') (g1' : b -->[g1] b') (f2' : a' -->[f2] a'') (g2' : b' -->[g2] b''), ((f1'⊗^{{TD}} g1') ;; (f2'⊗^{{TD}} g2')) = transportf _ (pfTensorComp x y x' y' x'' y'' f1 f2 g1 g2) ((f1';;f2') ⊗^{{TD}} (g1';;g2'))  .

  Definition displayed_triangle_identity {C : category} {T : tensor C} {I : C} {lu : left_unitor T I} {ru : right_unitor T I} {α : associator T} (tri : triangle_identity T I lu ru α) {D : disp_cat C} {TD : displayed_tensor T D} (i : D I) (dlu : displayed_leftunitor TD i lu) (dru : displayed_rightunitor TD i ru) (dα : displayed_associator α TD) := ∏ (x y : C), ∏ (a : D x) (b : D y),
      ((pr1 dα) x I y a i b) ;; ((id_disp a)  ⊗^{{TD}} (pr1 dlu) y b ) = transportb _ (tri x y) (((pr1 dru) x a) ⊗^{{TD}} id_disp b).

  Definition displayed_pentagon_identity {C : category} {T : tensor C} {α : associator T} (pen : pentagon_identity T α) {D : disp_cat C} {TD : displayed_tensor T D} (dα : displayed_associator α TD) : UU := ∏ (w x y z: C), ∏ (e : D w) (a : D x) (b : D y) (c : D z),
      (((pr1 dα) _ _ _ e a b) ⊗^{{TD}} (id_disp c)) ;; ((pr1 dα) _ _ _ e (a ⊗_{{TD}} b) c) ;; ((id_disp e) ⊗^{{TD}}  ((pr1 dα) _ _ _  a b c))  = transportb _ (pen w x y z) (((pr1 dα) (w ⊗_{T} x) y z (e ⊗_{{TD}} a) b c) ;; ((pr1 dα) w x (y ⊗_{T} z) e a (b ⊗_{{TD}} c))).

  Definition displayed_monoidal_category (M : monoidal_category) : UU :=
    ∑ (D : disp_cat M),
      ∑ (TD : displayed_tensor M D),
      ∑ (i : D (unit_extraction_of_monoidalcat M)),
      ∑ (dlu : displayed_leftunitor TD i (leftunitor_extraction_of_monoidalcat M)),
      ∑ (dru : displayed_rightunitor TD i (rightunitor_extraction_of_monoidalcat M)),
      ∑ (dα : displayed_associator (associator_extraction_of_monoidalcat M) TD),
      (displayed_tensor_functoriality_id (tensorfunctorid_identity_extraction_of_monoidalcat M) TD) × (displayed_tensor_functoriality_comp (tensorfunctorcomp_identity_extraction_of_monoidalcat M) TD) ×

      displayed_triangle_identity (triangleidentity_extraction_of_monoidalcat M) i dlu dru dα ×
                                  displayed_pentagon_identity (pentagonidentity_extraction_of_monoidalcat M) dα.
