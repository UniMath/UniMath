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

Section DisplayedCurriedMonoidalCategories.

  (* These notations come from 'MonoidalCategoriesCurried' *)
  Notation "x ⊗_{ T } y" := (tensoronobjects_from_tensor_cat T x y) (at level 31).
  Notation "f ⊗^{ T } g" := (tensoronmorphisms_from_tensor_cat T  _ _ _ _ f g) (at level 31).

  Definition displayed_tensor {C : category} (T : tensor C) (D : disp_cat C) :=
    ∑ (tensor_ob : ∏ (x y : C), (D x) → (D y) -> (D (x ⊗_{T} y))),
    ∏ (x x' y y' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y'),
      (a -->[f] a') -> (b -->[g] b') -> ((tensor_ob x y a b)-->[f ⊗^{T} g] (tensor_ob x' y' a' b')).

  Definition displayed_tensor_data :=
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

  Definition displayedtensor_on_morphisms_from_displayedtensor_data {C : category} {T : tensor C} {D : disp_cat C} (dtd : displayed_tensor T D) := pr2 dtd.
  Notation "f' ⊗^{{ dtd }} g'" := (displayedtensor_on_morphisms_from_displayedtensor_data dtd _ _ _ _ _ _ _ _ _ _ f' g'  ) (at level 31).

  Proposition total_category_has_tensor {C : category} (T : tensor C) (D : disp_cat C) (TD : displayed_tensor T D) :
    tensor (total_category D).
  Proof.
    unfold tensor.
    split with (λ xa yb, (pr1 xa) ⊗_{T} (pr1 yb) ,, (pr2 xa) ⊗_{{TD}} (pr2 yb)).
    intros xa yb xa' yb' f g.
    simpl.
    split with (pr1 f ⊗^{T} pr1 g).
    apply (pr2 TD).
    + exact (pr2 f).
    + exact (pr2 g).
  Defined.

  (* Remark::A unit for a displayed category D consists of the unit in C and a term in (D I), hence we do not need any special construction right now *)

  Definition displayed_leftunitor_on_objects {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (lu : left_unitor_on_objects T I) :=
    ∏ (x : C), ∏ (a : D x), ((i ⊗_{{TD}} a)-->[(lu x)] a).

  (* The following notation comes from 'DisplayedCats.Core' *)
  Notation "ff ;; gg" := (comp_disp ff gg) (at level 50, left associativity, format "ff ;; gg").

  Definition displayed_leftunitor_naturality {C : category} {T : tensor C} {I : C} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {lu : left_unitor T I} (dlu : displayed_leftunitor_on_objects TD i (pr1 lu)) :=
    ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b), (((id_disp i) ⊗^{{TD}} f') ;; (dlu y b)) = transportb _ ((pr2 lu) x y f) ((dlu x a) ;; f').

  Definition displayed_leftunitor {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (lu : left_unitor T I) :=
    ∑ (dlu : displayed_leftunitor_on_objects TD i (pr1 lu)), displayed_leftunitor_naturality dlu.

  Proposition total_category_has_leftunitor {C : category } {T : tensor C} {I : C} {lu : left_unitor T I} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} (dlu : displayed_leftunitor TD i lu):
    left_unitor (total_category_has_tensor T D TD) (I,,i).
  Proof.
    use tpair.
    + intro x.
      induction x as [x a].
      use tpair.
      - apply lu.
      - exact ((pr1 dlu) x a).
    +  simpl.
       intros x y f.
       induction x as [x a].
       induction y as [y b].
       induction f as [f f'].

       use total2_paths_b.
        - exact ((pr2 lu) x y f).
        - exact ((pr2 dlu) x y a b f f').
  Defined.

  Definition displayed_rightunitor_on_objects {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (ru : right_unitor_on_objects T I) :=
    ∏ (x : C), ∏ (a : D x), ((a ⊗_{{TD}} i)-->[(ru x)] a).

  Definition displayed_rightunitor_naturality {C : category} {T : tensor C} {I : C} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {ru : right_unitor T I} (dru : displayed_rightunitor_on_objects TD i (pr1 ru)) :=
    ∏ (x y : C), ∏ (a : D x) (b : D y) (f : C⟦x,y⟧) (f' : a -->[f] b),
      (( f' ⊗^{{TD}}  (id_disp i)) ;; (dru y b)) = transportb _ ((pr2 ru) x y f)   ((dru x a) ;; f').

  Definition displayed_rightunitor {C : category} {T : tensor C} {I : C} {D : disp_cat C} (TD : displayed_tensor T D) (i : D I) (ru : right_unitor T I) :=
    ∑ (dru : displayed_rightunitor_on_objects TD i (pr1 ru)), displayed_rightunitor_naturality dru.

  Proposition total_category_has_rightunitor {C : category } {T : tensor C} {I : C} {ru : right_unitor T I} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} (dru : displayed_rightunitor TD i ru):
    right_unitor (total_category_has_tensor T D TD) (I,,i).
  Proof.
    use tpair.
    + intro x.
      induction x as [x a].
      use tpair.
      - apply ru.
      - exact ((pr1 dru) x a).
    +  simpl.
       intros x y f.
       induction x as [x a].
       induction y as [y b].
       induction f as [f f'].
       cbn.

       use total2_paths_b.
        - exact ((pr2 ru) x y f).
        - exact ((pr2 dru) x y a b f f').
  Defined.

  Definition displayed_associator_on_objects {C : category} {T : tensor C} {D : disp_cat C} (TD : displayed_tensor T D) (α : associator_on_objects T) :=
    ∏ (x y z : C), ∏ (a : D x) (b : D y) (c : D z),
      ((a ⊗_{{TD}} b) ⊗_{{TD}} c) -->[(α x y z)] (a ⊗_{{TD}} (b ⊗_{{TD}} c)).

  Definition displayed_associator_naturality {C : category} {T : tensor C} {D : disp_cat C} {TD : displayed_tensor T D} {α : associator T} (dα : displayed_associator_on_objects TD (pr1 α)) :=
    ∏ (x x' y y' z z' : C), ∏ (a : D x) (a' : D x') (b : D y) (b' : D y') (c : D z) (c' : D z'),
      ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧), ∏ (f' : a-->[f] a') (g' : b -->[g] b') (h' : c -->[h] c'), (dα x y z a b c) ;; (f' ⊗^{{TD}} (g' ⊗^{{TD}} h')) =  transportb _ ((pr2 α) _ _ _ _ _ _ f g h) ( ((f' ⊗^{{TD}} g') ⊗^{{TD}} h') ;; dα _ _ _ a' b' c' ).

  Definition displayed_associator {C : category} {T : tensor C} (α : associator T) {D : disp_cat C} (TD : displayed_tensor T D) :=
    ∑ (dα_ob : displayed_associator_on_objects TD (pr1 α)), (displayed_associator_naturality dα_ob).

  Proposition total_category_has_associator {C : category } {T : tensor C} {α : associator T} {D : disp_cat C} {TD : displayed_tensor T D} (dα : displayed_associator α TD ):
    associator (total_category_has_tensor T D TD).
  Proof.
    use tpair.
    + unfold associator_on_objects.
      intros x y z.
      induction x as [x a].
      induction y as [y b].
      induction z as [z c].
      cbn.
      use tpair.
      - exact ((pr1 α) x y z).
      - exact ((pr1 dα) x y z a b c).
    + intros x x' y y' z z' f g h.
      induction x as [x a].
      induction x' as [x' a'].
      induction y as [y b].
      induction y' as [y' b'].
      induction z as [z c].
      induction z' as [z' c'].
      induction f as [f f'].
      induction g as [g g'].
      induction h as [h h'].
      use total2_paths_b.
      - exact ((pr2 α) x x' y y' z z' f g h).
      - exact ((pr2 dα) x x' y y' z z' a a' b b' c c' f g h f' g' h').
  Defined.

  Definition displayed_triangle_identity {C : category} {T : tensor C} {I : C} {lu : left_unitor T I} {ru : right_unitor T I} {α : associator T} (tri : triangle_identity T I lu ru α) {D : disp_cat C} {TD : displayed_tensor T D} (i : D I) (dlu : displayed_leftunitor TD i lu) (dru : displayed_rightunitor TD i ru) (dα : displayed_associator α TD) := ∏ (x y : C), ∏ (a : D x) (b : D y),
      ((pr1 dα) x I y a i b) ;; ((id_disp a)  ⊗^{{TD}} (pr1 dlu) y b ) = transportb _ (tri x y) (((pr1 dru) x a) ⊗^{{TD}} id_disp b).

  Proposition total_category_has_triangle_identity {C : category} {T : tensor C} {I : C} {lu : left_unitor T I} {ru : right_unitor T I} {α : associator T} {tri : triangle_identity T I lu ru α} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {dlu : displayed_leftunitor TD i lu} {dru : displayed_rightunitor TD i ru} {dα : displayed_associator α TD} (dtri : displayed_triangle_identity tri i dlu dru dα)
    : triangle_identity (total_category_has_tensor T D TD)  (I,,i) (total_category_has_leftunitor dlu) (total_category_has_rightunitor dru) (total_category_has_associator dα).
  Proof.
    unfold triangle_identity.
    intros x y.
    induction x as [x a].
    induction y as [y b].
    use total2_paths_b.
    + exact (tri x y).
    + exact (dtri x y a b).
  Defined.

  Definition displayed_pentagon_identity {C : category} {T : tensor C} {α : associator T} (pen : pentagon_identity T α) {D : disp_cat C} {TD : displayed_tensor T D} (dα : displayed_associator α TD) := ∏ (w x y z: C), ∏ (e : D w) (a : D x) (b : D y) (c : D z),
      (((pr1 dα) _ _ _ e a b) ⊗^{{TD}} (id_disp c)) ;; ((pr1 dα) _ _ _ e (a ⊗_{{TD}} b) c) ;; ((id_disp e) ⊗^{{TD}}  ((pr1 dα) _ _ _  a b c))  = transportb _ (pen w x y z) (((pr1 dα) (w ⊗_{T} x) y z (e ⊗_{{TD}} a) b c) ;; ((pr1 dα) w x (y ⊗_{T} z) e a (b ⊗_{{TD}} c))).

  Proposition total_category_has_pentagon_identity {C : category} {T : tensor C} {α : associator T} {pen : pentagon_identity T α} {D : disp_cat C} {TD : displayed_tensor T D} {dα : displayed_associator α TD} (dpen : displayed_pentagon_identity pen dα)
    : pentagon_identity (total_category_has_tensor T D TD) (total_category_has_associator dα).
  Proof.
    unfold pentagon_identity.
    intros w x y z.
    induction w as [w e].
    induction x as [x a].
    induction y as [y b].
    induction z as [z c].
    use total2_paths_b.
    + exact (pen w x y z).
    + exact (dpen w x y z e a b c).
  Defined.

  Definition displayed_monoidal_category {M : monoidal_category} (D : disp_cat M) :=
    ∑ (TD : displayed_tensor M D),
      ∑ (i : D (unit_extraction_of_monoidalcat M)),
      ∑ (dlu : displayed_leftunitor TD i (leftunitor_extraction_of_monoidalcat M)),
      ∑ (dru : displayed_rightunitor TD i (rightunitor_extraction_of_monoidalcat M)),
      ∑ (dα : displayed_associator (associator_extraction_of_monoidalcat M) TD),
      displayed_triangle_identity (triangleidentity_extraction_of_monoidalcat M) i dlu dru dα ×
      displayed_pentagon_identity (pentagonidentity_extraction_of_monoidalcat M) dα.

  Theorem total_category_is_monoidal {M : monoidal_category} {D : disp_cat M} (DM : displayed_monoidal_category D) : monoidal_category.
  Proof.
    unfold monoidal_category.
    split with (total_category D).
    split with (total_category_has_tensor M D (pr1 DM)).
    split with (unit_extraction_of_monoidalcat M ,, pr1 (pr2 DM)).
    split with (total_category_has_leftunitor (pr1 (pr2 (pr2 DM)))).
    split with (total_category_has_rightunitor (pr1 (pr2 (pr2 (pr2 DM))))).
    split with (total_category_has_associator (pr1 (pr2 (pr2 (pr2 (pr2 DM)))))).
    split with (total_category_has_triangle_identity (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DM))))))).
    exact (total_category_has_pentagon_identity (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM))))))).

  Defined.


End DisplayedCurriedMonoidalCategories.
