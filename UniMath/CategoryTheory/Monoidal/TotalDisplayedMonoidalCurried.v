(* In this file we show:
   1. If a displayed category over a monoidal category has the structure of a displayed monoidal category,
      then has the total category the structure of a monoidal category.
   2. The projection from the total category (equipped with this monoidal structure) to the base (monoidal) category
      is a strict monoidal functor.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalCurried.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsCurried.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

  Definition total_category_has_tensor {C : category} {T : tensor C} {D : disp_cat C} (TD : displayed_tensor T D) :
    tensor (total_category D).
  Proof.
    split with (λ xa yb, (pr1 xa) ⊗_{T} (pr1 yb) ,, (pr2 xa) ⊗_{{TD}} (pr2 yb)).
    intros xa yb xa' yb' f g.
    split with (pr1 f ⊗^{T} pr1 g).
    apply (pr2 TD).
    + exact (pr2 f).
    + exact (pr2 g).
  Defined.

  Proposition total_category_has_leftunitor {C : category } {T : tensor C} {I : C} {lu : left_unitor T I} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} (dlu : displayed_leftunitor TD i lu) :
    left_unitor (total_category_has_tensor TD) (I,,i).
  Proof.
    use tpair.
    + intro x.
      use tpair.
      - apply lu.
      - exact ((pr1 dlu) (pr1 x) (pr2 x)).
    +  abstract( intros x y f ;
       use total2_paths_b ;
                 [ exact ((pr2 lu) (pr1 x) (pr1 y) (pr1 f)) |
                   exact ((pr2 dlu) (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f)) ]).
  Defined.

  Proposition total_category_has_rightunitor {C : category } {T : tensor C} {I : C} {ru : right_unitor T I} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} (dru : displayed_rightunitor TD i ru) :
    right_unitor (total_category_has_tensor TD) (I,,i).
  Proof.
    use tpair.
    + intro x.
      use tpair.
      - apply ru.
      - exact ((pr1 dru) (pr1 x) (pr2 x)).
    +  abstract( intros x y f ;
       use total2_paths_b ;
        [ exact ((pr2 ru) (pr1 x) (pr1 y) (pr1 f)) |
          exact ((pr2 dru) (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f)) ]).
  Defined.

  Proposition total_category_has_associator {C : category } {T : tensor C} {α : associator T} {D : disp_cat C} {TD : displayed_tensor T D} (dα : displayed_associator α TD ) :
    associator (total_category_has_tensor TD).
  Proof.
    use tpair.
    + intros x y z.
      use tpair.
      - exact ((pr1 α) (pr1 x) (pr1 y) (pr1 z)).
      - exact ((pr1 dα) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)).
    + intros x x' y y' z z' f g h.
      use total2_paths_b.
      - exact ((pr2 α) (pr1 x) (pr1 x') (pr1 y) (pr1 y') (pr1 z) (pr1 z') (pr1 f) (pr1 g) (pr1 h)).
      - exact ((pr2 dα) (pr1 x) (pr1 x') (pr1 y) (pr1 y') (pr1 z) (pr1 z')
                        (pr2 x) (pr2 x') (pr2 y) (pr2 y') (pr2 z) (pr2 z')
                        (pr1 f) (pr1 g) (pr1 h) (pr2 f) (pr2 g) (pr2 h) ).
  Defined.

Proposition total_category_satisfied_tensor_functorialityid {C : category} {T : tensor C} {D : disp_cat C} {TD : displayed_tensor T D} {pfTensorId : tensor_functor_id T} (pfDTensorId : displayed_tensor_functoriality_id pfTensorId TD):
  tensor_functor_id (total_category_has_tensor TD).
Proof.
  intros x y.
  use total2_paths_f.
  + use pfTensorId.
  + use ((pfDTensorId (pr1 x) (pr1 y) (pr2 x) (pr2 y))).
Defined.

Proposition total_category_satisfied_tensor_functorialitycomp {C : category} {T : tensor C} {D : disp_cat C} {TD : displayed_tensor T D} {pfTensorComp : tensor_functor_comp T} (pfDTensorComp : displayed_tensor_functoriality_comp pfTensorComp TD):
  tensor_functor_comp (total_category_has_tensor TD).
Proof.
  intros x y x' y' x'' y'' f f' g g'.
  use total2_paths_f.
  + use pfTensorComp.
  + use (pathsinv0 ((pfDTensorComp (pr1 x) (pr1 y) (pr1 x') (pr1 y') (pr1 x'') (pr1 y'')
                         (pr2 x) (pr2 y) (pr2 x') (pr2 y') (pr2 x'') (pr2 y'')
                         (pr1 f) (pr1 g) (pr1 f') (pr1 g')
                         (pr2 f) (pr2 g) (pr2 f') (pr2 g')))). (* Converse some equality so that I don't have to use pathsinv0 *)
Defined.

  Proposition total_category_has_triangle_identity {C : category} {T : tensor C} {I : C} {lu : left_unitor T I} {ru : right_unitor T I} {α : associator T} {tri : triangle_identity T I lu ru α} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {dlu : displayed_leftunitor TD i lu} {dru : displayed_rightunitor TD i ru} {dα : displayed_associator α TD} (dtri : displayed_triangle_identity tri i dlu dru dα)
    : triangle_identity (total_category_has_tensor TD)  (I,,i) (total_category_has_leftunitor dlu) (total_category_has_rightunitor dru) (total_category_has_associator dα).
  Proof.
    intros x y.
    use total2_paths_b.
    + exact (tri (pr1 x) (pr1 y)).
    + exact (dtri (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Proposition total_category_has_pentagon_identity {C : category} {T : tensor C} {α : associator T} {pen : pentagon_identity T α} {D : disp_cat C} {TD : displayed_tensor T D} {dα : displayed_associator α TD} (dpen : displayed_pentagon_identity pen dα)
    : pentagon_identity (total_category_has_tensor TD) (total_category_has_associator dα).
  Proof.
    intros w x y z.
    use total2_paths_b.
    + exact (pen (pr1 w) (pr1 x) (pr1 y) (pr1 z)).
    + exact (dpen (pr1 w) (pr1 x) (pr1 y) (pr1 z) (pr2 w) (pr2 x) (pr2 y) (pr2 z)).
  Qed.


  Theorem total_category_is_monoidal {M : monoidal_category} (DM : displayed_monoidal_category M) : monoidal_category.
Proof.
    split with (total_category (pr1 DM)).
    split with (total_category_has_tensor (pr1 (pr2 DM))).
    split with (unit_extraction_of_monoidalcat M ,, pr1 (pr2 (pr2 DM))).
    split with (total_category_has_leftunitor (pr1 (pr2 (pr2 (pr2 DM))))).
    split with (total_category_has_rightunitor (pr1 (pr2 (pr2 (pr2 (pr2 DM)))))).
    split with (total_category_has_associator (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DM))))))).
    split with (total_category_satisfied_tensor_functorialityid (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM)))))))).
    split with (total_category_satisfied_tensor_functorialitycomp (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM))))))))).
    split with (total_category_has_triangle_identity (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM)))))))))).
    exact (total_category_has_pentagon_identity (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM)))))))))).
Defined.

Notation "π^{ D }" := (pr1_category D).

Definition monoidal_projection {M : monoidal_category} (DM : displayed_monoidal_category M) : functor (total_category_is_monoidal DM) M.
Proof.
  exact π^{pr1 DM}.
Defined.

Lemma projection_of_totalcategory_preservesunitstrictly {M : monoidal_category} (DM : displayed_monoidal_category M) :
  (strictly_unit_preserving_morphism (monoidal_projection DM)).
Proof.
  use tpair.
  + use (identity).
  + use tpair.
  - apply idpath.
  - apply idpath.
Defined.

Definition projection_of_totalcategory_preservestensorstrictly {M : monoidal_category} (DM : displayed_monoidal_category M) :
  (strictly_tensor_preserving_morphism (monoidal_projection DM)).
Proof.
  use tpair.
  + intros x y.
    use (identity).
  + intros x y.
    use tpair.
  - apply idpath.
  - apply idpath.
Defined.

Lemma projection_of_totalcategory_leftunitality {M : monoidal_category} (DM : displayed_monoidal_category M) :
  ∏ (x : (total_category_is_monoidal DM)), ((pr2 (pr1 (monoidal_projection DM))) _ _ ((pr1 (leftunitor_extraction_of_monoidalcat (total_category_is_monoidal DM))) x)) = ((pr1 (leftunitor_extraction_of_monoidalcat M)) (pr1 x)).
Proof.
  intro x.
  apply idpath.
Qed.

Lemma projection_of_totalcategory_associativity {M : monoidal_category} (DM : displayed_monoidal_category M) :
  ∏ (x y z : (total_category_is_monoidal DM)), ((pr2 (pr1 (monoidal_projection DM))) _ _ ((pr1 (associator_extraction_of_monoidalcat (total_category_is_monoidal DM))) x y z)) = ((pr1 (associator_extraction_of_monoidalcat M)) (pr1 x) (pr1 y) (pr1 z)).
Proof.
  intros x y z.
  apply idpath.
Qed.

Notation "T( M )" := (total_category_is_monoidal M).
Notation "α^{ C }_{ x , y , z }" := ((pr1 (associator_extraction_of_monoidalcat C)) x y z) (at level 31).
Notation "π^{ DM }( f )" := ((pr21 (monoidal_projection DM)) _ _ f).
Notation "π_{ DM }( x , y )" := (( ( pr1 (pr1 (pr2 _))) (monoidal_projection DM x) (monoidal_projection DM y)  )).
Notation "x ⊗_{ M } y" := ((pr1 (tensor_extraction_of_monoidalcat M)) x y).
Notation "f ⊗^{ M } g" := ((pr2 (tensor_extraction_of_monoidalcat M)) _ _ _ _ f g).

Lemma test {C : category} {x y  z w: C} (f : C⟦x,y⟧) (g : C⟦y,x⟧) (h : C⟦x,w⟧):
  ((f·g) = (identity x)) -> ((f · (g · h)) = h).
Proof.
  intro p.
  use (pathscomp0).
  + exact ((f·g)·h).
  + exact ((pr1 (pr2 (pr2 (pr1 C)))) _ _ _ _ f g h).
  + use pathscomp0.
  - exact ((identity x)·h).
  - induction p.
    use idpath.
  - use (((pr1 (pr1 (pr2 (pr1 C)))) x w ) h).
Qed.

Lemma projection_of_totalcategory_preservesleftunitality {M : monoidal_category} (DM : displayed_monoidal_category M) :
  preserves_leftunitality (projection_of_totalcategory_preservestensorstrictly DM) (projection_of_totalcategory_preservesunitstrictly DM).
Proof.
  intro x.
  cbn.
  set (I := unit_extraction_of_monoidalcat M). (* : M *)
  set (lu := pr1 (leftunitor_extraction_of_monoidalcat M)).

  use test.
  + exact (pr1 x).
  + set (p :=  (((pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))) I (pr1 x)))).
    set (q := ((pr2 (pr1 (pr2 (pr11 M)))) (I ⊗_{M} (pr1 x)) (I ⊗_{M} (pr1 x)) ((identity I) ⊗^{M} (identity (pr1 x))))).
    exact (q@p).
Defined.

Lemma projection_of_totalcategory_preservesrightunitality {M : monoidal_category} (DM : displayed_monoidal_category M) :
  preserves_rightunitality (projection_of_totalcategory_preservestensorstrictly DM) (projection_of_totalcategory_preservesunitstrictly DM).
Proof.
  intro x.
  cbn.
  set (I := unit_extraction_of_monoidalcat M). (* : M *)
  set (lu := pr1 (rightunitor_extraction_of_monoidalcat M)).

  use test.
  + exact (pr1 x).
  + set (p :=  (((pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))) (pr1 x) I))).
    set (q := ((pr2 (pr1 (pr2 (pr11 M)))) ((pr1 x) ⊗_{M} I) ((pr1 x) ⊗_{M} I) (((identity (pr1 x)) ⊗^{M} (identity I))))).
    exact (q@p).
Defined.

Notation "id_{ x }" := (identity x).

Lemma projection_of_totalcategory_preservesassociativity {M : monoidal_category} (DM : displayed_monoidal_category M) :
  preserves_associativity (projection_of_totalcategory_preservestensorstrictly DM).
Proof.
  intros x y z.
  induction x as [x a] ; induction y as [y b]; induction z as [z c].
  set (tid := (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))))).

  assert (pf0 : id_{ x ⊗_{ M} y} ⊗^{ M} id_{ z} · (id_{ (x ⊗_{ M} y) ⊗_{ M} z} · α^{ M }_{ x, y, z}) = id_{ (x ⊗_{ M} y) ⊗_{M} z} · (id_{ (x ⊗_{ M} y) ⊗_{ M} z} · α^{ M }_{ x, y, z})).
  { exact (cancel_postcomposition _ _ ( (id_{ (x ⊗_{ M} y) ⊗_{ M} z} · α^{ M }_{ x, y, z})) (( (tid (x⊗_{M} y) z)))). }

  assert (pf1 : id_{ (x ⊗_{ M} y) ⊗_{M} z} · (id_{ (x ⊗_{ M} y) ⊗_{ M} z} · α^{ M }_{ x, y, z}) =  (id_{ (x ⊗_{ M} y) ⊗_{ M} z} · α^{ M }_{ x, y, z})).
  {
    assert (intermid :  (id_{ (x ⊗_{ M} y) ⊗_{ M} z} · α^{ M }_{ x, y, z}) =  α^{ M }_{ x, y, z}). {
      exact ((pr1 (pr1 (pr2 (pr11 M))))  _ _ (α^{ M }_{ x, y, z})).
    }
    exact (cancel_precomposition _ _ _ _ _ _  (id_{ (x ⊗_{ M} y) ⊗_{ M} z}) intermid).
  }

  assert (pf2 : (id_{ (x ⊗_{M} y) ⊗_{M} z}) · (α^{ M }_{ x, y, z}) = (α^{M}_{x,y,z})).
  { exact ((pr1 (pr1 (pr2 (pr11 M))))  _ _ (α^{ M }_{ x, y, z})). }

  assert (pf3 : (α^{M}_{x,y,z}) = α^{M}_{x,y,z}· id_{x ⊗_{ M} (y ⊗_{ M} z)}).
  { exact (pathsinv0 ((pr2 (pr1 (pr2 (pr11 M))))  _ _ (α^{ M }_{ x, y, z}))). }

  assert (pf4 :  α^{M}_{x,y,z}· id_{x ⊗_{ M} (y ⊗_{ M} z)} = α^{M}_{x,y,z}· id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z}).
  { exact (cancel_precomposition _ _ _ _ _ _  (α^{M}_{x,y,z}) (pathsinv0 (tid x (y⊗_{M}z)))). }

  assert (pf5 :  α^{M}_{x,y,z}· id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z} =   (α^{ M }_{ x, y, z} · (id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z})) · id_{ x ⊗_{ M} (y ⊗_{ M} z)}).
  {  exact (pathsinv0 ((pr2 (pr1 (pr2 (pr1 (pr1 M))))) _ _ ( α^{M}_{x,y,z}· id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z} ))).  }

  assert (pf6 :   (α^{ M }_{ x, y, z} · (id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z})) · id_{ x ⊗_{ M} (y ⊗_{ M} z)} =  α^{ M }_{ x, y, z} · (id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z} · id_{ x ⊗_{ M} (y ⊗_{ M} z)})).
  { exact (assoc' (α^{ M }_{ x, y, z}) ( id_{ x} ⊗^{ M} id_{ y ⊗_{ M} z}) ( id_{ x ⊗_{ M} (y ⊗_{ M} z)})). }

  exact (pf0 @ pf1 @ pf2 @ pf3 @ pf4 @ pf5 @ pf6).
Qed.

Theorem projection_of_totalcategory_is_strict_monoidal_functor {M : monoidal_category} (DM : displayed_monoidal_category M) :
  strict_monoidal_functor (total_category_is_monoidal DM) M.
Proof.
  split with (monoidal_projection DM).
  use tpair.
  + unfold strictly_tensor_preserving_morphism.
    use tpair.
  - unfold weakly_tensor_preserving_morphism.
    intros x y.
    use identity.
  - intros x y.
    use tpair.
    -- apply idpath.
    -- apply idpath.
    + cbn.
      use tpair.
  - use tpair.
    -- use identity.
    -- use tpair.
       --- apply idpath.
       --- apply idpath.
  - use tpair.
    -- apply (projection_of_totalcategory_preservesassociativity DM).
    -- use tpair.
       --- apply (projection_of_totalcategory_preservesleftunitality DM).
       --- apply (projection_of_totalcategory_preservesrightunitality DM).
Qed.
