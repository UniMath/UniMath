(***************************************************************************************

 Functors between displayed categories of monomorphisms

 Every functor that preserves monomorphisms gives rise to a displayed functor between
 the displayed categories of mononomorphisms. We also show that this displayed functor
 is a weak equivalence if the original functor is one.

 Content
 1. Displayed functor between displayed categories of monomorphisms
 2. Conditions for which this functor is a weak equivalence
 3. Properties of the fiber functor

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.

Local Open Scope cat.

Section MonoCodomainFunctor.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          (HF : ∏ (x y : C₁) (f : x --> y), isMonic f → isMonic (#F f)).

  (** * 1. Displayed functor between displayed categories of monomorphisms *)
  Definition disp_mono_codomain_functor_data
    : disp_functor_data F (disp_mono_codomain C₁) (disp_mono_codomain C₂).
  Proof.
    simple refine (_ ,, _).
    - refine (λ x gy, make_mono_cod_fib_ob (make_Monic _ (#F (mono_cod_mor gy)) _)).
      abstract
        (apply HF ;
         apply MonicisMonic).
    - simple refine (λ x₁ x₂ gy₁ gy₂ f p, #F (pr1 p) ,, _).
      abstract
        (cbn ;
         rewrite <- !functor_comp ;
         apply maponpaths ;
         exact (pr2 p)).
  Defined.

  Definition disp_mono_codomain_functor
    : disp_functor F (disp_mono_codomain C₁) (disp_mono_codomain C₂).
  Proof.
    simple refine (_ ,, _).
    - exact disp_mono_codomain_functor_data.
    - abstract
        (split ; intros ; apply locally_propositional_mono_cod_disp_cat).
  Defined.

  (** * 2. Conditions for which this functor is a weak equivalence *)
  Proposition disp_mono_codomain_functor_ess_surj
              (HF' : essentially_surjective F)
              (HF'' : fully_faithful F)
    : disp_functor_disp_ess_surj disp_mono_codomain_functor.
  Proof.
    intros x gy.
    pose proof (HF' (mono_cod_dom gy)) as H.
    revert H.
    use factor_through_squash_hProp.
    intros z.
    induction z as [ z f ].
    simple refine (hinhpr (_ ,, _)).
    - use make_mono_cod_fib_ob.
      + exact z.
      + use make_Monic.
        * exact (fully_faithful_inv_hom HF'' z x (f · mono_cod_mor gy)).
        * abstract
            (intros w g h p ;
             use (invmaponpathsweq (make_weq _ (HF'' w z))) ; cbn ;
             use (cancel_z_iso _ _ f) ;
             use (MonicisMonic _ (mono_cod_mor gy)) ;
             rewrite !assoc' ;
             pose (maponpaths (λ z, #F z) p) as q ;
             cbn -[fully_faithful_inv_hom] in q ;
             rewrite !functor_comp in q ;
             refine (!_ @ q @ _) ;
             apply maponpaths ;
             apply (homotweqinvweq (make_weq _ (HF'' z x)))).
    - simple refine (_ ,, _).
      + refine (pr1 f ,, _).
        abstract
          (cbn ;
           rewrite id_right ;
           refine (!_) ;
           apply (homotweqinvweq (make_weq _ (HF'' z x)))).
      + use is_z_iso_disp_mono_codomain'.
        apply f.
  Qed.

  Proposition disp_mono_codomain_functor_ff
              (HF' : fully_faithful F)
    : disp_functor_ff disp_mono_codomain_functor.
  Proof.
    intros x₁ x₂ gy₁ gy₂ f.
    use isweqimplimpl.
    - intros ff.
      simple refine (_ ,, _).
      + exact (fully_faithful_inv_hom HF' _ _ (pr1 ff)).
      + use (invmaponpathsweq (make_weq _ (HF' _ _))).
        cbn -[fully_faithful_inv_hom].
        rewrite !functor_comp.
        refine (_ @ pr2 ff).
        apply maponpaths_2.
        apply (homotweqinvweq (make_weq _ (HF' _ _))).
    - apply locally_propositional_mono_cod_disp_cat.
    - apply locally_propositional_mono_cod_disp_cat.
  Qed.

  (** * 3. Properties of the fiber functor *)
  Proposition disp_mono_codomain_fiber_functor_essentially_surjective
              (HF' : essentially_surjective F)
              (HF'' : fully_faithful F)
              (x : C₁)
    : essentially_surjective (fiber_functor disp_mono_codomain_functor x).
  Proof.
    exact (fiber_functor_essentially_surjective
             _
             (disp_mono_codomain_functor_ess_surj HF' HF'')
             x).
  Qed.

  Proposition disp_mono_codomain_fiber_functor_ff
              (HF' : fully_faithful F)
              (x : C₁)
    : fully_faithful (fiber_functor disp_mono_codomain_functor x).
  Proof.
    exact (fiber_functor_ff _ (disp_mono_codomain_functor_ff HF') x).
  Qed.
End MonoCodomainFunctor.
