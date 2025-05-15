(**
   Let C be a category with binary products.
   In [CategoryTheory/exponentials.v], the theory of exponential objects has been developed using the language of adjunctions.
   In this file, we develop exponentials using universal arrows.
   This is used, e.g., to construct Rezk completions for cartesian closed categories.
   The characterization presented in this file, allows to reason about exponents of pairs of objects, without assuming that an object is exponentiable (wrt to all objects).

   - [IsExponentiableObject]: Definition of exponentiability via universal arrows
   - The equivalence between the adjoint and universal arrow definitions is proven in [IsExponentiableAsHasRightAdjoint]
   - [UniquenessUpToIso]: Exponents of two objects are isomorphic
   - [UniquenessUpToEq]: Exponents of two objects are equal, assuming univalence
   - [ExponentiabilityTransportsAlongIso]: If x ≅ x', then Exponentiating with x is equivalent to exponentiang with x'.
   - [PreservationOfExponentialObjects]:
     In [exponentials.v], preservation of exponentials is defined via the existence of an inverse map to a canonical map. Here, preservation of exponentials is defined via saying that the image of an exponent is again an exponent.
   - [ReflectionOfExponentialObjects]: Definition of reflection for exponential objects

   Remark:
   Some code be refactored by having more lemma's about universal arrows (as defined in [CategoryTheory/Adjunctions/Core.v]).

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.exponentials.

Local Open Scope cat.

Lemma is_universal_arrow_from_after_path_induction
  {D C : category} (S : D ⟶ C) (c : C) (r : D) (f₁ f₂ : C⟦S r, c⟧) (p : f₁ = f₂)
  : is_coreflection (make_coreflection_data r f₁) → is_coreflection (make_coreflection_data r f₂).
Proof.
  use (transportf (λ g, is_coreflection (r ,, g))).
  exact p.
Qed. (* or defined. *)

Section IsExponentiableObject.

  Context {C : category} (P : BinProducts C).

  Definition is_exponentiable_alt_uvp
    {x y e : C} (ev : C⟦P x e, y⟧) : UU
    := is_coreflection (make_coreflection_data (F := constprod_functor1 P x) e ev).

  (* Evaluation map + universal property *)
  Definition is_Exponent
    (x y e : C) : UU
    := ∑ (ev : C⟦P x e, y⟧), is_exponentiable_alt_uvp ev.

  (* The existence of the exponential [x,y] *)
  (* Definition Exponent (x y : C) : UU
    := ∑ e : C, is_Exponent x y e. *)

  Definition Exponent (x y : C) : UU
    := coreflection y (constprod_functor1 P x).
    
  Identity Coercion exponent_to_coreflection : Exponent >-> coreflection.

  (* The existence of exponentials [x, -] *)
  Definition is_exponentiable_alt (x : C) : UU
    := ∏ (y : C), Exponent x y.

End IsExponentiableObject.

Section IsExponentiableAsHasRightAdjoint.

  Context {C : category} (P : BinProducts C).

  Lemma is_exponentiable_alt_to_is_exponentiable (x : C)
    : is_exponentiable_alt P x → is_exponentiable P x.
  Proof.
    apply coreflections_to_is_left_adjoint.
  Defined.

  (* exact e.
    intro y.
    unfold is_exponentiable_alt in e.
    unfold Exponent' in e.
    Check make_coreflection _ (e y).
    unfold is_exponentiable_alt in e.

    (* use make_coreflection.
    - exists (pr1 (e y)).
      exact (pr12 (e y)).
    - intro ; intros ; apply (pr22 (e _)). *)
  Defined. *)

  Lemma is_exponentiable_to_uvp {x : C} (e: is_exponentiable P x)
    : ∏ y : C, is_exponentiable_alt_uvp P (exp_eval e y).
  Proof.
    exact (coreflection_is_coreflection (right_adjoint_weq_coreflections _ e y)).
  Defined.

  Lemma is_exponentiable_to_is_exponentiable_alt (x : C)
    : is_exponentiable P x → is_exponentiable_alt P x.
  Proof.
    intros e y.
    apply (right_adjoint_to_coreflection e).
  Defined.

End IsExponentiableAsHasRightAdjoint.

Section UniquenessUpToIso.

  Definition exponentials_unique_up_to_iso
    {C : category} (P : BinProducts C)
    {x y : C} {e e' : C}
    {ev : C⟦P x e, y⟧} {ev' : C⟦P x e', y⟧}
    (ev_uvp : is_exponentiable_alt_uvp P ev)
    (ev'_uvp : is_exponentiable_alt_uvp P ev')
    : z_iso e e'
    := coreflection_uniqueness_iso (make_coreflection _ ev_uvp) (make_coreflection _ ev'_uvp).

End UniquenessUpToIso.

Section UniquenessUpToEq.

  Lemma isaprop_Exponent
    {C : category} (P : BinProducts C)
    (x y : C)
    : is_univalent C → isaprop (Exponent P x y).
  Proof.
    intro C_univ.
    exact (isaprop_coreflection C_univ).
  Qed.

End UniquenessUpToEq.

(* Section ExponentiabilityTransportsAlongIso.

  Context {C : category} (P : BinProducts C)
    {x x' : C} (i : z_iso x x').

  Context {y : C} (e : Exponent P x y).

  Let ev : C⟦P x' (coreflection_data_object e), y⟧
      :=  BinProductOfArrows C (P x (coreflection_data_object e)) (P x' (coreflection_data_object e))
            (z_iso_inv i) (identity (coreflection_data_object e)) · e.

  Local Lemma equiv_of_mor
    {a : C}
    (f : C⟦P x' a, y⟧)
    (g : C⟦a, coreflection_data_object e⟧)
    : (f = BinProductOfArrows C (P x' (coreflection_data_object e)) (P x' a) (identity x') g · ev)
        ≃ (BinProductOfArrows C (P x' a) (P x a) i (identity a) · f
           = BinProductOfArrows C (P x (coreflection_data_object e)) (P x a) (identity x) g · e).
  Proof.
    use weqimplimpl.
    - intro pf.
      simpl in pf.
      etrans. {
        apply maponpaths.
        exact pf.
      }
      unfold ev.
      rewrite ! assoc.
      etrans. {
        do 2 apply maponpaths_2.
        apply BinProductOfArrows_comp.
      }
      etrans. {
        apply maponpaths_2.
        apply BinProductOfArrows_comp.
      }
      apply maponpaths_2.
      rewrite ! id_left.
      rewrite ! id_right.
      now rewrite z_iso_inv_after_z_iso.
    - intro pf.
      unfold ev.
      rewrite assoc.
      rewrite BinProductOfArrows_comp.
      apply pathsinv0.
      etrans. {
        apply maponpaths_2, maponpaths.
        refine (id_right _ @ _).
        exact (! id_left _).
      }
      etrans. {
        do 2 apply maponpaths_2.
        refine (id_left _ @ _).
        exact (! id_right _).
      }
      rewrite <- BinProductOfArrows_comp.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (! pf).
      }
      rewrite assoc.
      rewrite BinProductOfArrows_comp.
      rewrite id_right.
      rewrite z_iso_inv_after_z_iso.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply BinProductOfArrows_id.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Lemma Exponent_transport_along_iso
    : Exponent' P x' y.
  Proof.
    use make_coreflection.
    - use make_coreflection_data.
      + exact (coreflection_data_object e).
      + exact ev.
    - intro f.
      use (iscontrweqb' (coreflection_is_coreflection e (make_coreflection_data (coreflection_data_object f) (_ · f)))).
      + apply BinProductOfArrows.
        * exact i.
        * apply identity.
      + use weqfibtototal ; intro ; apply equiv_of_mor.
  Defined.

End ExponentiabilityTransportsAlongIso. *)

Section ExponentiabilityTransportsAlongIso'.

  Context {C : category} (P : BinProducts C)
    {x x' y y' : C}
    (i : z_iso x x')
    (j : z_iso y y').

  Context (e : Exponent P x y).

  (* Lemma equiv_of_mor'
    {a : C}
    (f : C ⟦ P x a, y'⟧)

    (g : C⟦a, coreflection_data_object e⟧)
    :  f = BinProductOfArrows C (P x (coreflection_data_object e)) (P x a) (identity x) g · (e · j)
             ≃ f · inv_from_z_iso j = BinProductOfArrows C (P x (coreflection_data_object e)) (P x a) (identity x) g · e.
    :  f = BinProductOfArrows C (P x (pr11 e)) (P x a) (identity x) g · (pr122 e · j)
             ≃ f · inv_from_z_iso j = BinProductOfArrows C (P x (pr11 e)) (P x a) (identity x) g · pr12 e.
  Proof.
  use weqimplimpl.
    - intro p.
      rewrite p.
      rewrite ! assoc'.
      rewrite z_iso_inv_after_z_iso.
      now rewrite id_right.
    - intro p.
      rewrite assoc.
      refine (_ @ maponpaths (λ x, x · _) p).
      rewrite assoc'.
      rewrite z_iso_after_z_iso_inv.
      now rewrite id_right.
    - apply homset_property.
    - apply homset_property.
  Qed. *)

  Lemma Exponent_transport_along_iso'
    : Exponent P x' y'.
  Proof.
    use (coreflection_transport_along_iso_ob_functor j (F := constprod_functor1 P x) _ e). *)
    (* apply (Exponent_transport_along_iso P i).
    use make_coreflection.
    - use make_coreflection_data.
      + exact (coreflection_data_object e).
      + exact (e · j).
    - intro f.
      use (iscontrweqb' (coreflection_is_coreflection e (make_coreflection_data (coreflection_data_object f) (f · z_iso_inv j)))).
      use weqfibtototal ; intro ; apply equiv_of_mor'. *)
  Defined.

End ExponentiabilityTransportsAlongIso'.

Lemma is_exponentiable_alt_closed_under_iso
  {C : category} (P : BinProducts C)
  {x x' : C} (i : z_iso x x')
  (e : is_exponentiable_alt P x)
  : is_exponentiable_alt P x'.
Proof.
  exact (λ y, Exponent_transport_along_iso' P i (identity_z_iso y) (e y)).
Defined.

Section IsExponentAlongIso.

  Context {C : category} {P : BinProducts C}
    {x y e' : C} (e : Exponent P x y) (i : z_iso e' (coreflection_data_object e)). (* (ee : is_Exponent P x y e). *)

  Local Lemma commutativity_of_evaluation_along_iso
    {a : C}
    (f : C⟦constprod_functor1 P x a, y⟧)
    (f' : C ⟦ a, e'⟧)
    : f = BinProductOfArrows C (P x e') (P x a) (identity x) f'
            · (BinProductOfArrows C (P x _) (P x e') (identity x) i · coreflection_data_arrow e)
      → f = BinProductOfArrows C (P x _) (P x a) (identity x) (f' · i) · coreflection_data_arrow e.
  Proof.
    intro pf.
    refine (pf @ _).
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans. { apply BinProductOfArrows_comp. }
    cbn ; unfold BinProduct_of_functors_mor ; cbn.
    apply maponpaths_2.
    apply id_right.
  Qed.

  Lemma is_Exponent_along_iso_uvp
    : is_exponentiable_alt_uvp P
        (BinProductOfArrows C (P x _) (P x e') (identity x) i · coreflection_data_arrow e).
  Proof.
    intro f.
    use (iscontrweqb' (coreflection_is_coreflection e f)).
    use weqtotal2.
    { apply z_iso_comp_left_weq ; exact i. }
    intro.
    use weqimplimpl.
    - apply commutativity_of_evaluation_along_iso.
    - intro pf.
      refine (pf @ _).
      apply pathsinv0.
      apply commutativity_of_evaluation_along_iso.
      cbn ; unfold BinProduct_of_functors_mor ; cbn.
      apply idpath.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Lemma is_Exponent_along_iso
    : is_Exponent P x y e'.
  Proof.
    use tpair.
    - refine (_ · coreflection_data_arrow e).
      apply binproduct_of_z_iso.
      + apply identity_z_iso.
      + exact i.
    - exact is_Exponent_along_iso_uvp.
  Defined.

End IsExponentAlongIso.

Section EvaluationMapsDoNotFormAProposition.
  (*
    Let C be a univalent cartesian category.
    Consider two objects x and y.
    An object e is the exponent of x and y provided an evaluation map which is suitably universal.
    By univalence, one might expect that the type witnessing "e is an exponent" is a proposition.
    However, this is false.
    This section makes explicit where this fails (we do not give a counter example).
   *)

  Context {C : category} (P : BinProducts C) (C_univ : is_univalent C).

  Lemma evaluation_unique_up_to_iso
    {x y e : C}
    {ev ev' : C ⟦ P x e, y ⟧}
    (ev_uvp : is_exponentiable_alt_uvp P ev)
    (ev'_uvp : is_exponentiable_alt_uvp P ev')
    : ∑ q : z_iso e e, ev = BinProductOfArrows _ _ _ (identity _) q · ev'.
  Proof.
    use tpair.
    - exact (exponentials_unique_up_to_iso P ev_uvp ev'_uvp).
    - exact (pr2 (iscontrpr1 (ev'_uvp (e ,, ev)))).
  Defined.

  Lemma binproductofarrows_idtoiso {x y e : C} (f : C⟦P x e, y⟧) (p : e = e)
    : BinProductOfArrows C (P x e) (P x e) (identity x) (idtoiso p) · f = f.
  Proof.
  Abort.

  Lemma isaprop_is_Exponent (x y e: C)
    : isaprop (is_Exponent P x y e).
  Proof.
    use isaproptotal2.
    { intro ev. apply isaprop_is_coreflection. }
    intros ev ev' ev_uvp ev'_uvp.
    set (q := evaluation_unique_up_to_iso ev_uvp ev'_uvp).
    induction q as [q₀ q₁].
    set (p := isotoid _ C_univ q₀).
    rewrite <- (idtoiso_isotoid _ C_univ _ _ q₀) in q₁.
    refine (q₁ @ _).
    (* apply binproductofarrows_idtoiso. *)
  Abort.

End EvaluationMapsDoNotFormAProposition.

Section PreservationOfExponentialObjects.

  Context {C₀ C₁ : category} (P₀ : BinProducts C₀) (P₁ : BinProducts C₁)
    {F : functor C₀ C₁} (F_pP : preserves_binproduct F).

  Definition preserves_exponential_objects : UU
    := ∏ (x y e : C₀) (ev : C₀⟦P₀ x e, y⟧),
      is_exponentiable_alt_uvp P₀ ev
      → is_exponentiable_alt_uvp P₁
          (z_iso_inv (preserves_binproduct_to_z_iso _ F_pP (P₀ _ _) (P₁ _ _)) · #F ev).

  Definition preserves_exponential_objects_to_exponent
    (F_pE : preserves_exponential_objects)
    : ∏ x y : C₀, Exponent P₀ x y → Exponent P₁ (F x) (F y).
  Proof.
    intros x y e.
    set (t := F_pE x y (coreflection_data_object e) e (coreflection_is_coreflection e)).
    exact (make_coreflection _ t).
  Defined.

  Definition preserves_exponential_objects' (E₀ : Exponentials P₀) : UU
    := ∏ (x y : C₀), is_exponentiable_alt_uvp P₁
                       (z_iso_inv (preserves_binproduct_to_z_iso _ F_pP (P₀ _ _) (P₁ _ _))
                          · #F (exp_eval (E₀ x) y)).

  Definition preserves_exponential_objects_to_exponent' {E₀ : Exponentials P₀}
    (F_pE : preserves_exponential_objects' E₀)
    : ∏ x y : C₀, Exponent P₁ (F x) (F y).
  Proof.
    intros x y.
    set (t := F_pE x y).
    exact (make_coreflection _ t).
  Defined.

  Definition preserves_exponential_objects_to_iso
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    (F_pE : preserves_exponential_objects) (x₀ y₀ : C₀)
    : z_iso (F (exp (E₀ x₀) y₀)) (exp (E₁ (F x₀)) (F y₀)).
  Proof.
    refine (exponentials_unique_up_to_iso P₁ _ _).
    - apply F_pE.
      exact (coreflection_is_coreflection (is_exponentiable_to_is_exponentiable_alt P₀ x₀ (E₀ x₀) y₀)).
    - exact (coreflection_is_coreflection (is_exponentiable_to_is_exponentiable_alt P₁ (F x₀) (E₁ (F x₀)) (F y₀))).
  Defined.

  Definition preserves_exponential_objects_to_iso'
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    (F_pE : preserves_exponential_objects' E₀) (x₀ y₀ : C₀)
    : z_iso (F (exp (E₀ x₀) y₀)) (exp (E₁ (F x₀)) (F y₀)).
  Proof.
    refine (exponentials_unique_up_to_iso P₁ _ _).
    - apply F_pE.
    - exact (coreflection_is_coreflection (is_exponentiable_to_is_exponentiable_alt P₁ (F x₀) (E₁ (F x₀)) (F y₀))).
  Defined.

  Lemma preserves_exponential_objects_to_preserves_exponentials
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    : preserves_exponential_objects' E₀ → preserves_exponentials E₀ E₁ F_pP.
  Proof.
    intros F_pE x₀ y₀.
    exact (is_z_isomorphism_path (idpath _)
             (pr2 (preserves_exponential_objects_to_iso' E₀ E₁ F_pE x₀ y₀))).
  Defined.

  Lemma preserves_exponentials_to_exponent
    {E₀ : Exponentials P₀} {E₁ : Exponentials P₁}
    (F_pE : preserves_exponentials E₀ E₁ F_pP)
    : ∏ x y : C₀, is_Exponent P₁ (F x) (F y) (F (exp (E₀ x) y)).
  Proof.
    intros x y.
    set (i := make_z_iso' _ (F_pE x y)).
    apply (is_Exponent_along_iso (right_adjoint_to_coreflection (E₁ _) _) i).

    (* apply (is_Exponent_along_iso _ i).
    refine (_ ,, _).
    exact (is_exponentiable_to_uvp P₁ (E₁ _) (F y)). *)
  Defined.

  Lemma preserves_exponentials_to_preserves_exponential_objects
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    : preserves_exponentials E₀ E₁ F_pP → preserves_exponential_objects' E₀.
  Proof.
    intros F_pE x y f₁.
    use (iscontrweqb' (pr2 (preserves_exponentials_to_exponent F_pE x y) f₁)).
    use weqfibtototal.
    intro.
    use weqimplimpl.
    - intro pf.
      refine (pf @ _).
      apply maponpaths.
      apply pathsinv0, exp_beta.
    - intro pf.
      refine (pf @ _).
      apply maponpaths.
      apply exp_beta.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Lemma preserves_exponential_objects'_to_preserves_exponential_objects
    {E₀ : Exponentials P₀}
    (F_pE : preserves_exponential_objects' E₀)
    : preserves_exponential_objects.
  Proof.
    intros x y e ev ev_uvp.

    use is_universal_arrow_from_after_path_induction.
    - refine (_ · z_iso_inv
          (preserves_binproduct_to_z_iso F F_pP (P₀ x (exp (E₀ x) y)) (P₁ (F x) (F (exp (E₀ x) y))))
          · # F (exp_eval (E₀ x) y)).
      apply BinProductOfArrows.
      { apply identity. }
      apply #F.
      use (exponentials_unique_up_to_iso P₀ ev_uvp).
      + apply exp_eval.
      + apply is_exponentiable_to_uvp.
    - rewrite <- functor_id.
      etrans. {
        apply maponpaths_2.
        apply pathsinv0.
        apply (preserves_binproduct_of_arrows F_pP (identity x) (exponentials_unique_up_to_iso P₀ ev_uvp (is_exponentiable_to_uvp P₀ (E₀ x) y))).
      }
      rewrite assoc'.
      etrans. { apply maponpaths, pathsinv0, functor_comp. }
      do 2 apply maponpaths.
      apply exp_beta.
    - intros f.
      set (ee := _ ,, F_pE x y : is_Exponent P₁ _ _ _).
      set (ee' := make_coreflection _ (F_pE x y) : Exponent P₁ _ _).

      set (s := is_Exponent_along_iso_uvp ee' (functor_on_z_iso F (exponentials_unique_up_to_iso P₀ ev_uvp (is_exponentiable_to_uvp P₀ (E₀ x) y)))).
      rewrite assoc'.
      exact (s f).
  Qed.

End PreservationOfExponentialObjects.

Section ReflectionOfExponentialObjects.

  Context {C₀ C₁ : category} (P₀ : BinProducts C₀) (P₁ : BinProducts C₁)
    {F : functor C₀ C₁} (F_pP : preserves_binproduct F).

  Definition reflects_exponential_objects : UU
    := ∏ (x y e : C₀) (ev : C₀⟦P₀ x e, y⟧),
      is_exponentiable_alt_uvp P₁
        (z_iso_inv (preserves_binproduct_to_z_iso _ F_pP (P₀ _ _) (P₁ _ _)) · #F ev)
      → is_exponentiable_alt_uvp P₀ ev.

End ReflectionOfExponentialObjects.
