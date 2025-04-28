(**
   Let C be a category with binary products.
   In [CategoryTheory/exponentials.v], the theory of exponential objects has been developed using the language of adjunctions.
   In this file, we develop exponentials using universal arrows.
   This is used, e.g., to construct Rezk completions for cartesian closed categories.
   The characterization presented in this file, is necessary to obtain propositions (or at least, make some proofs easier).

   - [IsExponentiableObject]: Definition of exponentiability via universal arrows
   - The equivalence between the adjoint and universal arrow definitions is proven in [IsExponentiableAsHasRightAdjoint]
   - [UniquenessUpToIso]: Exponents of two objects are isomorphic
   - [UniquenessUpToEq]: Exponents of two objects are equal, assuming univalence
   - [ExponentiabilityTransportsAlongIso]: If x ≅ x', then Exponentiating with x is equivalent to exponentiang with x'.
   - [PreservationOfExponentialObjects]:
     In [exponentials.v], preservation of exponentials is defined via the existence of an inverse map to a canonical map. Here, preservation of exponentials is defined via saying that the image of an exponent is again an exponent.

   Remark:
   Some code be refactored by having more lemma's about universal arrows.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.

Local Open Scope cat.

Section PrelimUniversalArrowFrom.

  Lemma is_universal_arrow_from_after_path_induction
    {D C : category} (S : D ⟶ C) (c : C) (r : D) (f₁ f₂ : C⟦S r, c⟧) (p : f₁ = f₂)
    : is_universal_arrow_from S c r f₁ → is_universal_arrow_from S c r f₂.
  Proof.
    induction p.
    apply idfun.
  Qed. (* or defined. *)


End PrelimUniversalArrowFrom.

Section PrelimTransport.

  Lemma transportf_BinProductOfArrows_right
    {C : category}
    (P : BinProducts C)
    {x y : C}
    {x₁ x₂ : C}
    (f : C⟦P x x₁, y⟧)
    (p : x₁ = x₂)
    : transportf (λ z : C, C ⟦ P x z, y⟧) p f =
        BinProductOfArrows C (P x x₁) (P x x₂) (identity x) (idtoiso (! p)) · f.
  Proof.
    induction p.
    cbn.
    rewrite BinProductOfArrows_id.
    exact (! id_left _).
  Qed.

End PrelimTransport.

Section PrelimProducts.
  (* This section has to be moved to Limits.BinProducts.v *)

  Definition BinProductOfArrows_iso
    {C : category}
    {x x' y y' : C}
    (P' : BinProduct _ x' y')
    (P : BinProduct _ x y)
    {fx : C⟦x, x'⟧} {fy : C⟦y, y'⟧}
    (i_fx : is_z_isomorphism fx) (i_fy : is_z_isomorphism fy)
    : is_z_isomorphism (BinProductOfArrows _ P' P fx fy).
  Proof.
    set (f_x_i := make_z_iso' _ i_fx).
    set (f_y_i := make_z_iso' _ i_fy).

    use make_is_z_isomorphism.
    { exact (BinProductOfArrows _ _ _ (z_iso_inv f_x_i) (z_iso_inv f_y_i)). }
    exact (binproduct_of_z_iso_inv P P' f_x_i f_y_i).
  Defined.

  Definition BinProductOfArrowsIsos'
    {C : category}
    {x x' y y' : C}
    (P' : BinProduct _ x' y')
    (P : BinProduct _ x y)
    {fx : C⟦x, x'⟧} {fy : C⟦y, y'⟧}
    (i_fx : is_z_isomorphism fx) (i_fy : is_z_isomorphism fy)
    : z_iso _ _
    := make_z_iso' _ (BinProductOfArrows_iso P' P i_fx i_fy).

  Definition BinProductOf_isos
    {C : category} (P : BinProducts C)
    {x x' y y' : C} {fx : C⟦x, x'⟧} {fy : C⟦y, y'⟧}
    (i_fx : is_z_isomorphism fx) (i_fy : is_z_isomorphism fy)
    : is_z_isomorphism (BinProductOfArrows _ (P x' y') (P x y) fx fy).
  Proof.
    set (f_x_i := make_z_iso' _ i_fx).
    set (f_y_i := make_z_iso' _ i_fy).

    use make_is_z_isomorphism.
    { exact (BinProductOfArrows _ _ _ (z_iso_inv f_x_i) (z_iso_inv f_y_i)). }
    exact (binproduct_of_z_iso_inv (P x y) (P x' y') f_x_i f_y_i).
  Defined.

  Definition BinProductOfIsos
    {C : category} (P : BinProducts C)
    {x x' y y' : C} {fx : C⟦x, x'⟧} {fy : C⟦y, y'⟧}
    (i_fx : is_z_isomorphism fx) (i_fy : is_z_isomorphism fy)
    : z_iso (P x y) (P x' y')
    := make_z_iso _ _ (BinProductOf_isos P i_fx i_fy).

End PrelimProducts.

Section IsExponentiableObject.

  Context {C : category} (P : BinProducts C).

  Definition is_exponentiable_alt_uvp
    {x y e : C} (ev : C⟦P x e, y⟧) : UU
    := is_universal_arrow_from (constprod_functor1 P x) y e ev.

  (* Evaluation map + universal property *)
  Definition is_Exponent
    (x y e : C) : UU
    := ∑ (ev : C⟦P x e, y⟧), is_exponentiable_alt_uvp ev.

  (* The existence of the exponential [x,y] *)
  Definition Exponent (x y : C) : UU
    := ∑ e : C, is_Exponent x y e.

  (* The existence of exponentials [x, -] *)
  Definition is_exponentiable_alt (x : C) : UU
    := ∏ (y : C), Exponent x y.

End IsExponentiableObject.

Section IsExponentiableAsHasRightAdjoint.

  Context {C : category} (P : BinProducts C).

  Lemma is_exponentiable_alt_to_is_exponentiable (x : C)
    : is_exponentiable_alt P x → is_exponentiable P x.
  Proof.
    intro e.
    use left_adjoint_from_partial.
    - exact (λ y, pr1 (e y)).
    - exact (λ y, pr12 (e y)).
    - intro ; intro ; intros ; apply (pr22 (e _)).
  Defined.

  Lemma is_exponentiable_to_uvp {x : C} (e: is_exponentiable P x)
    : ∏ y : C, is_exponentiable_alt_uvp P (exp_eval e y).
  Proof.
    intro y.
    set (l := left_adjoint_to_adjunction e).
    set (ll := make_are_adjoints _ _ _ _ (pr2 l)).
    set (lw := nathomweq_from_adj ll).
    intros a f.
    set (lww := pr2 (invweq (hom_weq lw)) f).
    use (iscontrweqb' lww).
    use weqfibtototal.
    intro g.
    apply weqpathsinv0.
  Defined.

  Lemma is_exponentiable_to_is_exponentiable_alt (x : C)
    : is_exponentiable P x → is_exponentiable_alt P x.
  Proof.
    intros e y.
    simple refine (_ ,, _ ,, _).
    - exact (exp e y).
    - exact (exp_eval e y).
    - apply is_exponentiable_to_uvp.
  Defined.

End IsExponentiableAsHasRightAdjoint.

Section UniquenessUpToIso.

  Context {C : category} (P : BinProducts C).

  Lemma unique_maps_between_evaluation_maps_form_inverses
    {x y e e' : C}
    {ev : C ⟦ P x e, y ⟧}
    {ev' : C ⟦ P x e', y ⟧}
    (ev_uvp : is_exponentiable_alt_uvp P ev)
    (ev'_uvp : is_exponentiable_alt_uvp P ev')
    : pr1 (iscontrpr1 (ev'_uvp e ev)) · pr1 (iscontrpr1 (ev_uvp e' ev')) = identity e.
  Proof.
    refine (_ @ idpath (pr1 (iscontrpr1 (ev_uvp e ev))) @ _).
    - use (base_paths _ _ (pr2 (ev_uvp e ev) (_ ,, _))).
      simpl.
      etrans.
      2: {
        apply maponpaths_2.
        apply BinProductOfArrows_idxcomp.
      }
      rewrite assoc'.
      etrans.
      2: {
        apply maponpaths.
        exact (pr21 (ev_uvp e' ev')).
      }
      apply (pr21 (ev'_uvp _ _)).
    - use (! base_paths _ _ (pr2 (ev_uvp e ev) (_ ,, _))).
      refine (! id_left _ @ _).
      apply maponpaths_2.
      apply pathsinv0, BinProductOfArrows_id.
  Qed.

  Lemma exponentials_unique_up_to_iso
    {x y : C} {e e' : C}
    {ev : C⟦P x e, y⟧} {ev' : C⟦P x e', y⟧}
    (ev_uvp : is_exponentiable_alt_uvp P ev)
    (ev'_uvp : is_exponentiable_alt_uvp P ev')
    : z_iso e e'.
  Proof.
    use make_z_iso.
      - exact (pr1 (iscontrpr1 (ev'_uvp e ev))).
      - exact (pr1 (iscontrpr1 (ev_uvp e' ev'))).
      - split ; apply unique_maps_between_evaluation_maps_form_inverses.
  Defined.

End UniquenessUpToIso.

Section UniquenessUpToEq.

  Context {C : category} (P : BinProducts C).

  Lemma equality_of_exponentials
    {x y : C}
    (ϕ₁ ϕ₂ : Exponent P x y)
    (p : pr1 ϕ₁ = pr1 ϕ₂)
    (q : BinProductOfArrows _ _ _ (identity _) (idtoiso (! p)) · (pr12 ϕ₁) = pr12 ϕ₂)
    : ϕ₁ = ϕ₂.
  Proof.
    use (total2_paths_f p).
    use total2_paths_f.
    {
      refine (_ @ q).
      unfold is_Exponent ; rewrite pr1_transportf.
      apply transportf_BinProductOfArrows_right.
    }
    use proofirrelevance.
    do 2 (apply impred_isaprop ; intro) ; apply isapropiscontr.
  Qed.

  Lemma isaprop_Exponent (x y : C)
    : is_univalent C → isaprop (Exponent P x y).
  Proof.
    intro C_univ.
    use invproofirrelevance.
    intros ϕ₁ ϕ₂.
    use equality_of_exponentials.
    - use (isotoid _ C_univ).
      exact (exponentials_unique_up_to_iso P (pr22 ϕ₁) (pr22 ϕ₂)).
    - rewrite inv_isotoid, idtoiso_isotoid.
      exact (! pr21 (pr22 ϕ₁ _ (pr12 ϕ₂))).
  Qed.

End UniquenessUpToEq.

Section ExponentiabilityTransportsAlongIso.

  Context {C : category} (P : BinProducts C)
    {x x' : C} (i : z_iso x x').

  Context {y : C} (e : Exponent P x y).

  Let ev : C⟦P x' (pr1 e), y⟧
      :=  BinProductOfArrows C (P x (pr1 e)) (P x' (pr1 e))
            (z_iso_inv i) (identity (pr1 e)) · pr12 e.

  Local Lemma equiv_of_mor
    {a : C}
    (f : C⟦P x' a, y⟧)
    (g : C⟦a, pr1 e⟧)
    : (f = BinProductOfArrows C (P x' (pr1 e)) (P x' a) (identity x') g · ev)
        ≃ (BinProductOfArrows C (P x' a) (P x a) i (identity a) · f
           = BinProductOfArrows C (P x (pr1 e)) (P x a) (identity x) g · pr12 e).
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
    : Exponent P x' y.
  Proof.
    exists (pr1 e).
    exists ev.
    intros a f.
    use (iscontrweqb' (pr22 e a (_ · f))).
    - apply BinProductOfArrows.
      + exact i.
      + apply identity.
    - use weqfibtototal ; intro ; apply equiv_of_mor.
  Defined.

End ExponentiabilityTransportsAlongIso.

Section ExponentiabilityTransportsAlongIso'.

  Context {C : category} (P : BinProducts C)
    {x x' y y' : C}
    (i : z_iso x x')
    (j : z_iso y y').

  Context (e : Exponent P x y).

  Lemma equiv_of_mor'
    {a : C}
    (f : C ⟦ P x a, y'⟧)
    (g : C⟦a, pr1 e⟧)
    :  f = BinProductOfArrows C (P x (pr1 e)) (P x a) (identity x) g · (pr12 e · j)
             ≃ f · inv_from_z_iso j = BinProductOfArrows C (P x (pr1 e)) (P x a) (identity x) g · pr12 e.
  Proof.
    use weqimplimpl.
    - intro p.
      rewrite p.
      rewrite ! assoc'.
      rewrite z_iso_inv_after_z_iso.
      now rewrite id_right.
    - intro p.
      rewrite assoc.
      rewrite <- p.
      rewrite assoc'.
      rewrite z_iso_after_z_iso_inv.
      now rewrite id_right.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Lemma Exponent_transport_along_iso'
    : Exponent P x' y'.
  Proof.
    use (Exponent_transport_along_iso P i).
    exists (pr1 e).
    exists (pr12 e · j).
    intros a f.
    use (iscontrweqb' (pr22 e a (f · z_iso_inv j))).
    use weqfibtototal ; intro ; apply equiv_of_mor'.
  Defined.

End ExponentiabilityTransportsAlongIso'.

Lemma is_exponentiable_alt_closed_under_iso
  {C : category} (P : BinProducts C)
  {x x' : C} (i : z_iso x x')
  (e : is_exponentiable_alt P x)
  : is_exponentiable_alt P x'.
Proof.
  exact (λ y, Exponent_transport_along_iso P i (e y)).
Defined.

Section IsExponentAlongIso.

  Context {C : category} {P : BinProducts C}
    {x y e e' : C} (i : z_iso e' e) (ee : is_Exponent P x y e).

  Local Lemma commutativity_of_evaluation_along_iso
    {a : C}
    (f : C⟦constprod_functor1 P x a, y⟧)
    (f' : C ⟦ a, e' ⟧)
    : f = BinProductOfArrows C (P x e') (P x a) (identity x) f'
            · (BinProductOfArrows C (P x e) (P x e') (identity x) i · pr1 ee)
      → f = BinProductOfArrows C (P x e) (P x a) (identity x) (f' · i) · pr1 ee.
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
        (BinProductOfArrows C (P x e) (P x e') (identity x) i · pr1 ee).
  Proof.
    intros a f.
    use (iscontrweqb' (pr2 ee a f)).
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
    - refine (_ · pr1 ee).
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
    - exact (pr2 (iscontrpr1 (ev'_uvp _ ev))).
  Defined.

  Lemma binproductofarrows_idtoiso {x y e : C} (f : C⟦P x e, y⟧) (p : e = e)
    : BinProductOfArrows C (P x e) (P x e) (identity x) (idtoiso p) · f = f.
  Proof.
  Abort.

  Lemma isaprop_is_Exponent (x y e: C)
    : isaprop (is_Exponent P x y e).
  Proof.
    use isaproptotal2.
    { intro ev ; do 2 (apply impred_isaprop ; intro) ; apply isapropiscontr. }
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
    set (t := F_pE x y (pr1 e) (pr12 e) (pr22 e)).
    exact (_ ,, _ ,, t).
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
    exact (_ ,, _ ,, t).
  Defined.

  Definition preserves_exponential_objects_to_iso
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    (F_pE : preserves_exponential_objects) (x₀ y₀ : C₀)
    : z_iso (F (exp (E₀ x₀) y₀)) (exp (E₁ (F x₀)) (F y₀)).
  Proof.
    refine (exponentials_unique_up_to_iso P₁ _ _).
    - apply F_pE.
      exact (pr22 (is_exponentiable_to_is_exponentiable_alt P₀ x₀ (E₀ x₀) y₀)).
    - exact (pr22 (is_exponentiable_to_is_exponentiable_alt P₁ (F x₀) (E₁ (F x₀)) (F y₀))).
  Defined.

  Definition preserves_exponential_objects_to_iso'
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    (F_pE : preserves_exponential_objects' E₀) (x₀ y₀ : C₀)
    : z_iso (F (exp (E₀ x₀) y₀)) (exp (E₁ (F x₀)) (F y₀)).
  Proof.
    refine (exponentials_unique_up_to_iso P₁ _ _).
    - apply F_pE.
    - exact (pr22 (is_exponentiable_to_is_exponentiable_alt P₁ (F x₀) (E₁ (F x₀)) (F y₀))).
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
    apply (is_Exponent_along_iso i).
    refine (_ ,, _).
    exact (is_exponentiable_to_uvp P₁ (E₁ _) (F y)).
  Defined.

  Lemma preserves_exponentials_to_preserves_exponential_objects
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁)
    : preserves_exponentials E₀ E₁ F_pP → preserves_exponential_objects' E₀.
  Proof.
    intros F_pE x y a₁ f₁.
    set (e := _ ,, preserves_exponentials_to_exponent F_pE x y : Exponent P₁ (F x) (F y)).
    use (iscontrweqb' (pr22 e a₁ f₁)).
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
    - intros d f.
      set (ee := _ ,, F_pE x y : is_Exponent P₁ _ _ _).
      set (s := is_Exponent_along_iso_uvp  (functor_on_z_iso F (exponentials_unique_up_to_iso P₀ ev_uvp (is_exponentiable_to_uvp P₀ (E₀ x) y))) ee).
      rewrite assoc'.
      exact (s d f).
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
