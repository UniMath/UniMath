(**

 Full subcategories of displayed categories

 Suppose that we have a displayed category `D` over `C`, and suppose that we also have
 - a predicate `P` on the objects of `C`
 - a predicate `Q` on the objects of `D` over objects of `C` satisfying `P`
 We construct a displayed category over the full subcategory of `C` whose objects over
 `x` are objects `xx : D x` that satisfy `Q`. We also provide various kinds of structure
 on this displayed category, such as a cleaving.

 Our interest in this construction comes from comprehension categories. Specifically,
 we can use this construction to define subcomprehension categories where we restrict
 our comprehension category to types and contexts satisfying some property.

 Contents
 1. The displayed category
 2. Univalence of this displayed category
 3. A cleaving for this displayed category
 4. A comprehension functor
 5. Useful lemmas
 6. Fiberwise finite limits
 7. Properties of the inclusion

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.

Local Open Scope cat.

Section FullSubDispCat.
  Context {C : category}
          (D : disp_cat C)
          (P : C → UU)
          (Q : ∏ (x : C), P x → D x → UU).

  (** * 1. The displayed category *)
  Definition full_sub_disp_cat_ob_mor
    : disp_cat_ob_mor (full_subcat C P).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, ∑ (xx : D (pr1 x)), Q (pr1 x) (pr2 x) xx).
    - exact (λ x y xx yy f, pr1 xx -->[ pr1 f ] pr1 yy).
  Defined.

  Definition full_sub_disp_cat_id_comp
    : disp_cat_id_comp (full_subcat C P) full_sub_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x xx, id_disp _).
    - exact (λ x y z f g xx yy zz ff gg, ff ;; gg)%mor_disp.
  Defined.

  Definition full_sub_disp_cat_data
    : disp_cat_data (full_subcat C P).
  Proof.
    simple refine (_ ,, _).
    - exact full_sub_disp_cat_ob_mor.
    - exact full_sub_disp_cat_id_comp.
  Defined.

  Proposition transportf_full_sub_disp_cat
              {x y : full_subcat C P}
              {f g : x --> y}
              (p : f = g)
              {xx : full_sub_disp_cat_data x}
              {yy : full_sub_disp_cat_data y}
              (ff : xx -->[ f ] yy)
    : transportf (λ h, _ -->[ h ] _) p ff
      =
      transportf (λ h, pr1 xx -->[ h ] pr1 yy) (maponpaths pr1 p) ff.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_full_sub_disp_cat
              {x y : full_subcat C P}
              {f g : x --> y}
              (p : f = g)
              {xx : full_sub_disp_cat_data x}
              {yy : full_sub_disp_cat_data y}
              (ff : xx -->[ g ] yy)
    : transportb (λ h, _ -->[ h ] _) p ff
      =
      transportb (λ h, pr1 xx -->[ h ] pr1 yy) (maponpaths pr1 p) ff.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition full_sub_disp_cat_axioms
    : disp_cat_axioms (full_subcat C P) full_sub_disp_cat_data.
  Proof.
    repeat split.
    - intros.
      refine (_ @ !(transportb_full_sub_disp_cat _ _)).
      cbn.
      rewrite id_left_disp.
      apply maponpaths_2.
      apply homset_property.
    - intros.
      refine (_ @ !(transportb_full_sub_disp_cat _ _)).
      cbn.
      rewrite id_right_disp.
      apply maponpaths_2.
      apply homset_property.
    - intros.
      refine (_ @ !(transportb_full_sub_disp_cat _ _)).
      cbn.
      rewrite assoc_disp.
      apply maponpaths_2.
      apply homset_property.
    - intros.
      apply homsets_disp.
  Qed.

  Definition full_sub_disp_cat
    : disp_cat (full_subcat C P).
  Proof.
    simple refine (_ ,, _).
    - exact full_sub_disp_cat_data.
    - exact full_sub_disp_cat_axioms.
  Defined.

  (**
   An alternative definition would be

    sigma_disp_cat
      (disp_full_sub
        (total_category
        (reindex_disp_cat (pr1_category (disp_full_sub C P)) D))
        (λ xx, Q (pr11 xx) (pr21 xx) (pr2 xx)))

  We do not use this definition, because composition on displayed morphisms is
  defined in this displayed category using `transport` (due to reindexing)
  whereas in our definition, no `transport` is needed.
   *)

  Definition full_subcat_incl
    : full_subcat C P ⟶ C
    := pr1_category _.

  Definition full_sub_disp_cat_incl_data
    : disp_functor_data
        full_subcat_incl
        full_sub_disp_cat
        D.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, pr1 xx).
    - exact (λ x y xx yy f ff, ff).
  Defined.

  Proposition full_sub_disp_cat_incl_laws
    : disp_functor_axioms full_sub_disp_cat_incl_data.
  Proof.
    split ; intros ; cbn.
    - refine (!_).
      apply transportf_set.
      apply homset_property.
    - refine (!_).
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition full_sub_disp_cat_incl
    : disp_functor
        full_subcat_incl
        full_sub_disp_cat
        D.
  Proof.
    simple refine (_ ,, _).
    - exact full_sub_disp_cat_incl_data.
    - exact full_sub_disp_cat_incl_laws.
  Defined.

  Proposition fiber_functor_full_sub_disp_cat_incl
              {x : full_subcat C P}
              (xx₁ xx₂ : full_sub_disp_cat x)
              (ff : xx₁ -->[ identity _ ] xx₂)
    : #(fiber_functor full_sub_disp_cat_incl _) ff = ff.
  Proof.
    cbn.
    apply transportf_set.
    apply homset_property.
  Qed.

  (** * 2. Univalence of this displayed category *)
  Definition full_sub_disp_cat_is_z_iso_weq
             {x : full_subcat C P}
             (xx₁ xx₂ : full_sub_disp_cat x)
             (ff : xx₁ -->[ identity _ ] xx₂)
    : is_z_iso_disp (identity_z_iso (pr1 x)) ff
      ≃
      is_z_iso_disp (identity_z_iso x) ff.
  Proof.
    use weqimplimpl.
    - intro Hf.
      refine (pr1 Hf ,, _ ,, _).
      + abstract
          (refine (_ @ !(transportb_full_sub_disp_cat _ _)) ;
           refine (pr12 Hf @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
      + abstract
          (refine (_ @ !(transportb_full_sub_disp_cat _ _)) ;
           refine (pr22 Hf @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
    - intro Hf.
      refine (pr1 Hf ,, _ ,, _).
      + abstract
          (refine (pr12 Hf @ _) ;
           refine (transportb_full_sub_disp_cat _ _ @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
      + abstract
          (refine (pr22 Hf @ _) ;
           refine (transportb_full_sub_disp_cat _ _ @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
    - apply isaprop_is_z_iso_disp.
    - apply isaprop_is_z_iso_disp.
  Defined.

  Definition full_sub_disp_cat_z_iso_weq
             {x : full_subcat C P}
             (xx₁ xx₂ : full_sub_disp_cat x)
    : z_iso_disp (identity_z_iso (pr1 x)) (pr1 xx₁) (pr1 xx₂)
      ≃
      z_iso_disp (identity_z_iso x) xx₁ xx₂.
  Proof.
    use weqfibtototal.
    exact (full_sub_disp_cat_is_z_iso_weq xx₁ xx₂).
  Defined.

  Proposition is_univalent_full_sub_disp_cat
              (HD : is_univalent_disp D)
              (HQ : ∏ (x : C) (p : P x) (xx : D x), isaprop (Q x p xx))
    : is_univalent_disp full_sub_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros x xx₁ xx₂.
    use weqhomot.
    - refine (full_sub_disp_cat_z_iso_weq xx₁ xx₂
              ∘ make_weq _ (HD _ _ (idpath _) (pr1 xx₁) (pr1 xx₂))
              ∘ path_sigma_hprop _ _ _ _)%weq.
      apply HQ.
    - intro p.
      induction p.
      use eq_z_iso_disp.
      cbn.
      apply idpath.
  Qed.

  (** * 3. A cleaving for this displayed category *)
  Definition cleaving_full_sub_disp_cat
             (HD : cleaving D)
             (HQ : ∏ (x y : C)
                     (f : y --> x)
                     (xx : D x)
                     (px : P x)
                     (py : P y)
                       (qxx : Q x px xx),
                   Q y py (HD _ _ f xx))
    : cleaving full_sub_disp_cat.
  Proof.
    intros x y f xx.
    simple refine (_ ,, _ ,, _).
    - simple refine (_ ,, _).
      + exact (HD _ _ (pr1 f) (pr1 xx)).
      + exact (HQ _ _ (pr1 f) _ (pr2 x) (pr2 y) (pr2 xx)).
    - exact (HD _ _ (pr1 f) (pr1 xx)).
    - intros w g ww hh.
      use make_iscontr.
      + simple refine (_ ,, _).
        * exact (cartesian_factorisation (HD _ _ (pr1 f) (pr1 xx)) _ hh).
        * abstract
            (cbn ;
             apply cartesian_factorisation_commutes).
      + abstract
          (intro hh' ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           use (cartesian_factorisation_unique (HD _ _ (pr1 f) (pr1 xx))) ; cbn ;
           rewrite cartesian_factorisation_commutes ;
           apply (pr2 hh')).
  Defined.

  (** * 4. A comprehension functor *)
  Section Comprehension.
    Context (χ : disp_functor (functor_identity C) D (disp_codomain C))
            (Hχ : ∏ (x : C)
                    (xx : D x)
                    (p : P x),
                  Q x p xx → P (pr1 (χ x xx))).

    Definition full_sub_disp_cat_comprehension_data
      : disp_functor_data
          (functor_identity _)
          full_sub_disp_cat
          (disp_codomain _).
    Proof.
      simple refine (_ ,, _).
      - simple refine (λ x xx, _ ,, _).
        + simple refine (_ ,, _).
          * exact (pr1 (χ (pr1 x) (pr1 xx))).
          * exact (Hχ _ _ _ (pr2 xx)).
        + refine (_ ,, tt).
          exact (pr2 (χ (pr1 x) (pr1 xx))).
      - simple refine (λ x y xx yy f ff, _ ,, _).
        + refine (_ ,, tt).
          exact (pr1 (♯ χ ff)%mor_disp).
        + abstract
            (use full_subcat_mor_eq ; cbn ;
             exact (pr2 (♯ χ ff)%mor_disp)).
    Defined.

    Proposition full_sub_disp_cat_comprehension_laws
      : disp_functor_axioms full_sub_disp_cat_comprehension_data.
    Proof.
      split.
      - intros x xx.
        use eq_cod_mor.
        rewrite transportb_cod_disp.
        use full_subcat_mor_eq.
        cbn.
        exact (maponpaths pr1 (disp_functor_id χ (pr1 xx))).
      - intros x y z xx yy zz f g ff gg.
        use eq_cod_mor.
        rewrite transportb_cod_disp.
        use full_subcat_mor_eq.
        cbn.
        exact (maponpaths pr1 (disp_functor_comp χ ff gg)).
    Qed.

    Definition full_sub_disp_cat_comprehension
      : disp_functor
          (functor_identity _)
          full_sub_disp_cat
          (disp_codomain _).
    Proof.
      simple refine (_ ,, _).
      - exact full_sub_disp_cat_comprehension_data.
      - exact full_sub_disp_cat_comprehension_laws.
    Defined.

    Definition is_cartesian_full_sub_disp_cat_comprehension
               (HD : cleaving D)
               (HQ : ∏ (x y : C)
                       (f : y --> x)
                       (xx : D x)
                       (px : P x)
                       (py : P y)
                       (qxx : Q x px xx),
                     Q y py (HD _ _ f xx))
               (χ_cart : is_cartesian_disp_functor χ)
      : is_cartesian_disp_functor
          full_sub_disp_cat_comprehension.
    Proof.
      use is_cartesian_disp_functor_chosen_lifts.
      {
        exact (cleaving_full_sub_disp_cat HD HQ).
      }
      intros x y f yy.
      use isPullback_cartesian_in_cod_disp.
      use full_subcat_is_pullback.
      use cartesian_isPullback_in_cod_disp.
      use χ_cart.
      cbn.
      exact (HD (pr1 y) (pr1 x) (pr1 f) (pr1 yy)).
    Defined.

    Definition full_sub_cod_weq
               {x y : full_subcat C P}
               (xx : full_sub_disp_cat x)
               (yy : full_sub_disp_cat y)
               (f : x --> y)
      : χ (pr1 x) (pr1 xx) -->[ pr1 f ] χ (pr1 y) (pr1 yy)
        ≃
        full_sub_disp_cat_comprehension x xx
        -->[ f ]
        full_sub_disp_cat_comprehension y yy.
    Proof.
      use weq_iso.
      - refine (λ ff, (pr1 ff ,, tt) ,, _).
        abstract
          (use full_subcat_mor_eq ;
           exact (pr2 ff)).
      - refine (λ ff, pr11 ff ,, _).
        abstract
          (exact (maponpaths pr1 (pr2 ff))).
      - abstract
          (intro ff ;
           use eq_cod_mor ;
           cbn ;
           apply idpath).
      - abstract
          (intro ff ;
           use eq_cod_mor ;
           use full_subcat_mor_eq ;
           cbn ;
           apply idpath).
    Defined.

    Definition disp_functor_ff_full_sub_disp_cat_comprehension
               (χ_ff : disp_functor_ff χ)
      : disp_functor_ff full_sub_disp_cat_comprehension.
    Proof.
      intros x y xx yy f.
      use weqhomot.
      - exact (full_sub_cod_weq xx yy f
                ∘ make_weq _ (χ_ff _ _ (pr1 xx) (pr1 yy) (pr1 f)))%weq.
      - abstract
          (intro ff ;
           use eq_cod_mor ;
           apply idpath).
    Defined.
  End Comprehension.

  (** * 5. Useful lemmas *)
  Proposition comp_full_sub_disp_cat_fib
              {x : full_subcat C P}
              {xx yy zz : full_sub_disp_cat [{x}]}
              (ff : xx --> yy)
              (gg : yy --> zz)
    : ff · gg = compose (C := D[{pr1 x}]) ff gg.
  Proof.
    refine (transportf_full_sub_disp_cat _ _ @ _).
    cbn.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition full_sub_disp_cat_fiber_functor_from_cleaving
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
              (HD' := cleaving_full_sub_disp_cat HD HQ)
              {x y : full_subcat C P}
              (f : x --> y)
              {yy₁ yy₂ : full_sub_disp_cat [{y}]}
              (ff : yy₁ --> yy₂)
    : # (fiber_functor_from_cleaving full_sub_disp_cat HD' f) ff
      =
      # (fiber_functor_from_cleaving _ HD (pr1 f)) ff.
  Proof.
    simpl.
    apply maponpaths.
    refine (transportf_full_sub_disp_cat _ (_ ;; _)%mor_disp @ _).
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition is_z_isomorphism_fiber_full_sub_disp_cat
             {x : full_subcat C P}
             {xx₁ xx₂ : full_sub_disp_cat x}
             (f : (fiber_category full_sub_disp_cat x) ⟦ xx₁ , xx₂ ⟧)
             (g : is_z_isomorphism (C := fiber_category D (pr1 x)) f)
    : is_z_isomorphism f.
  Proof.
    refine (pr1 g ,, _ ,, _).
    - abstract
        (refine (_ @ pr12 g) ;
         rewrite comp_full_sub_disp_cat_fib ;
         apply idpath).
    - abstract
        (refine (_ @ pr22 g) ;
         rewrite comp_full_sub_disp_cat_fib ;
         apply idpath).
  Defined.

  Definition full_sub_disp_cat_fiber_z_iso
              {x : full_subcat C P}
              {xx yy : full_sub_disp_cat [{x}]}
              (ff : z_iso (C := D[{pr1 x}]) (pr1 xx) (pr1 yy))
    : z_iso xx yy.
  Proof.
    refine (pr1 ff ,, _).
    apply is_z_isomorphism_fiber_full_sub_disp_cat.
    exact (pr2 ff).
  Defined.

  Proposition fiber_functor_from_cleaving_comp_full_sub_disp_cat
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
              {x y z : full_subcat C P}
              (f : y --> x)
              (g : z --> y)
              (xx : full_sub_disp_cat[{x}])
    : fiber_functor_from_cleaving_comp (cleaving_full_sub_disp_cat HD HQ) f g xx
      =
      fiber_functor_from_cleaving_comp HD (pr1 f) (pr1 g) (pr1 xx).
  Proof.
    simpl.
    apply maponpaths.
    etrans.
    {
      apply transportb_full_sub_disp_cat.
    }
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition fiber_functor_on_eq_full_sub_disp_cat
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
              {x y : full_subcat C P}
              {f g : x --> y}
              (p : f = g)
              (yy : full_sub_disp_cat[{y}])
    : fiber_functor_on_eq (cleaving_full_sub_disp_cat HD HQ) p yy
      =
      fiber_functor_on_eq HD (maponpaths pr1 p) (pr1 yy).
  Proof.
    induction p.
    apply idpath.
  Qed.

  Proposition fiber_functor_from_cleaving_comp_inv_full_sub_disp_cat
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
              {x y z : full_subcat C P}
              (f : y --> x)
              (g : z --> y)
              (xx : full_sub_disp_cat[{x}])
    : fiber_functor_from_cleaving_comp_inv (cleaving_full_sub_disp_cat HD HQ) f g xx
      =
      fiber_functor_from_cleaving_comp_inv HD (pr1 f) (pr1 g) (pr1 xx).
  Proof.
    unfold fiber_functor_from_cleaving_comp_inv.
    do 2 apply maponpaths.
    etrans.
    {
      apply transportf_full_sub_disp_cat.
    }
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition comm_nat_z_iso_full_sub_disp_cat
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
              {w x y z : full_subcat C P}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (q : pr1 k · pr1 f = pr1 h · pr1 g)
              (ww : full_sub_disp_cat[{w}])
    : comm_nat_z_iso (cleaving_full_sub_disp_cat HD HQ) f g h k p ww
      =
      comm_nat_z_iso HD _ _ _ _ q (pr1 ww).
  Proof.
    rewrite !comm_nat_z_iso_ob.
    rewrite !comp_full_sub_disp_cat_fib.
    rewrite fiber_functor_from_cleaving_comp_full_sub_disp_cat.
    rewrite fiber_functor_on_eq_full_sub_disp_cat.
    rewrite fiber_functor_from_cleaving_comp_inv_full_sub_disp_cat.
    apply maponpaths_2.
    apply maponpaths.
    assert (q = maponpaths pr1 p) as ->.
    {
      apply homset_property.
    }
    apply idpath.
  Qed.

  Proposition comm_nat_z_iso_inv_full_sub_disp_cat
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
              {w x y z : full_subcat C P}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (q : pr1 k · pr1 f = pr1 h · pr1 g)
              (ww : full_sub_disp_cat[{w}])
    : comm_nat_z_iso_inv (cleaving_full_sub_disp_cat HD HQ) f g h k p ww
      =
      comm_nat_z_iso_inv HD _ _ _ _ q (pr1 ww).
  Proof.
    rewrite !comm_nat_z_iso_inv_ob.
    rewrite !comp_full_sub_disp_cat_fib.
    rewrite fiber_functor_from_cleaving_comp_full_sub_disp_cat.
    rewrite fiber_functor_on_eq_full_sub_disp_cat.
    rewrite fiber_functor_from_cleaving_comp_inv_full_sub_disp_cat.
    apply maponpaths_2.
    apply maponpaths.
    rewrite maponpathsinv0.
    assert (q = maponpaths pr1 p) as ->.
    {
      apply homset_property.
    }
    apply idpath.
  Qed.

  (** * 6. Fiberwise finite limits *)
  Section Terminal.
    Context (HD : cleaving D)
            (HQ : ∏ (x y : C)
                    (f : y --> x)
                    (xx : D x)
                    (px : P x)
                    (py : P y)
                      (qxx : Q x px xx),
                  Q y py (HD _ _ f xx))
            (T : fiberwise_terminal HD)
            (HT : ∏ (x : C) (p : P x), Q x p (terminal_obj_in_fib T x)).

    Definition full_sub_disp_cat_fiber_terminal
               (x : full_subcat C P)
      : Terminal (full_sub_disp_cat [{x}]).
    Proof.
      use make_Terminal.
      - simple refine (_ ,, _).
        + exact (terminal_obj_in_fib T (pr1 x)).
        + apply HT.
      - intros xx.
        use make_iscontr.
        + exact (TerminalArrow (terminal_in_fib T (pr1 x)) (pr1 xx)).
        + abstract
            (intro f ;
             exact (TerminalArrowUnique (terminal_in_fib T (pr1 x)) (pr1 xx) f)).
    Defined.

    Proposition preserves_terminal_full_sub_disp_cat_fiber_functor
                {x y : full_subcat C P}
                (f : x --> y)
      : preserves_terminal
          (fiber_functor_from_cleaving
             full_sub_disp_cat
             (cleaving_full_sub_disp_cat HD HQ)
             f).
    Proof.
      use preserves_terminal_if_preserves_chosen.
      {
        apply full_sub_disp_cat_fiber_terminal.
      }
      use iso_to_Terminal.
      {
        apply full_sub_disp_cat_fiber_terminal.
      }
      use full_sub_disp_cat_fiber_z_iso.
      cbn.
      use z_iso_inv.
      apply (preserves_terminal_to_z_iso _ (pr2 T (pr1 x) (pr1 y) (pr1 f))).
    Qed.

    Definition full_sub_disp_cat_fiberwise_terminal
      : fiberwise_terminal (cleaving_full_sub_disp_cat HD HQ).
    Proof.
      split.
      - exact full_sub_disp_cat_fiber_terminal.
      - intros x y f.
        apply preserves_terminal_full_sub_disp_cat_fiber_functor.
    Defined.
  End Terminal.

  Section BinProducts.
    Context (HD : cleaving D)
            (HQ : ∏ (x y : C)
                    (f : y --> x)
                    (xx : D x)
                    (px : P x)
                    (py : P y)
                    (qxx : Q x px xx),
                  Q y py (HD _ _ f xx))
            (BP : fiberwise_binproducts HD)
            (HBP : ∏ (x : C)
                     (px : P x)
                     (xx₁ xx₂ : D x)
                     (qxx₁ : Q x px xx₁)
                     (qxx₂ : Q x px xx₂),
                   Q x px (BinProductObject _ (binprod_in_fib BP xx₁ xx₂))).

    Definition full_sub_disp_cat_fiber_binproducts
               (x : full_subcat C P)
      : BinProducts (full_sub_disp_cat [{x}]).
    Proof.
      intros xx yy.
      use make_BinProduct.
      - simple refine (_ ,, _).
        + exact (BinProductObject _ (binprod_in_fib BP (pr1 xx) (pr1 yy))).
        + apply HBP.
          * exact (pr2 xx).
          * exact (pr2 yy).
      - exact (BinProductPr1 _ (binprod_in_fib BP (pr1 xx) (pr1 yy))).
      - exact (BinProductPr2 _ (binprod_in_fib BP (pr1 xx) (pr1 yy))).
      - intros ww ff gg.
        use make_iscontr.
        + simple refine (_ ,, _ ,, _).
          * exact (BinProductArrow _ (binprod_in_fib BP (pr1 xx) (pr1 yy)) ff gg).
          * abstract
              (rewrite comp_full_sub_disp_cat_fib ;
               apply (BinProductPr1Commutes _ _ _ (binprod_in_fib BP (pr1 xx) (pr1 yy)))).
          * abstract
              (refine (comp_full_sub_disp_cat_fib _ _ @ _) ;
               apply (BinProductPr2Commutes _ _ _ (binprod_in_fib BP (pr1 xx) (pr1 yy)))).
        + abstract
            (intro ξ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use ((BinProductArrowUnique _ _ _ (binprod_in_fib BP (pr1 xx) (pr1 yy)))) ;
             [ refine (_ @ pr12 ξ)
             | refine (_ @ pr22 ξ) ] ;
             rewrite comp_full_sub_disp_cat_fib ;
             apply idpath).
    Defined.

    Proposition preserves_binproduct_full_sub_disp_cat_fiber_functor
                {x y : full_subcat C P}
                (f : x --> y)
      : preserves_binproduct
          (fiber_functor_from_cleaving
             full_sub_disp_cat
             (cleaving_full_sub_disp_cat HD HQ)
             f).
    Proof.
      use preserves_binproduct_if_preserves_chosen.
      {
        apply full_sub_disp_cat_fiber_binproducts.
      }
      intros xx yy.
      use (isBinProduct_z_iso
             (isBinProduct_BinProduct
                _
                (full_sub_disp_cat_fiber_binproducts x _ _))).
      - use full_sub_disp_cat_fiber_z_iso.
        apply (preserves_binproduct_to_z_iso _ (pr2 BP (pr1 x) (pr1 y) (pr1 f))).
      - cbn -[fiber_category fiber_functor_from_cleaving].
        rewrite full_sub_disp_cat_fiber_functor_from_cleaving.
        rewrite comp_full_sub_disp_cat_fib.
        refine (!_).
        apply (BinProductPr1Commutes
                 _ _ _
                 (binprod_in_fib
                    BP
                    (HD _ _ (pr1 f) (pr1 xx))
                    (HD _ _(pr1 f) (pr1 yy)))).
      - cbn -[fiber_category fiber_functor_from_cleaving].
        rewrite full_sub_disp_cat_fiber_functor_from_cleaving.
        rewrite comp_full_sub_disp_cat_fib.
        refine (!_).
        apply (BinProductPr2Commutes
                 _ _ _
                 (binprod_in_fib
                    BP
                    (HD _ _ (pr1 f) (pr1 xx))
                    (HD _ _(pr1 f) (pr1 yy)))).
    Qed.

    Definition full_sub_disp_cat_fiberwise_binproducts
      : fiberwise_binproducts (cleaving_full_sub_disp_cat HD HQ).
    Proof.
      split.
      - exact full_sub_disp_cat_fiber_binproducts.
      - intros.
        apply preserves_binproduct_full_sub_disp_cat_fiber_functor.
    Defined.
  End BinProducts.

  Section Equalizers.
    Context (HD : cleaving D)
            (HQ : ∏ (x y : C)
                    (f : y --> x)
                    (xx : D x)
                    (px : P x)
                    (py : P y)
                       (qxx : Q x px xx),
                  Q y py (HD _ _ f xx))
            (E : fiberwise_equalizers HD)
            (HE : ∏ (x : C)
                    (px : P x)
                    (xx₁ xx₂ : D x)
                    (qxx₁ : Q x px xx₁)
                    (qxx₂ : Q x px xx₂)
                    (ff gg : xx₁ -->[ identity _ ] xx₂),
                  Q x px (EqualizerObject (equalizer_in_fib E ff gg))).

    Definition full_sub_disp_cat_fiber_equalizers
               (x : full_subcat C P)
      : Equalizers (full_sub_disp_cat [{x}]).
    Proof.
      intros xx yy ff gg.
      use make_Equalizer.
      - simple refine (_ ,, _).
        + exact (EqualizerObject (equalizer_in_fib E ff gg)).
        + apply HE.
          * exact (pr2 xx).
          * exact (pr2 yy).
      - exact (EqualizerArrow (equalizer_in_fib E ff gg)).
      - abstract
          (rewrite !comp_full_sub_disp_cat_fib ;
           apply (EqualizerEqAr (equalizer_in_fib E ff gg))).
      - intros ww hh p.
        use make_iscontr.
        + simple refine (_ ,, _).
          * use (EqualizerIn (equalizer_in_fib E ff gg) (pr1 ww) hh).
            abstract
              (refine (_ @ p @ _) ;
               rewrite comp_full_sub_disp_cat_fib ;
               apply idpath).
          * abstract
              (refine (_ @ EqualizerCommutes (equalizer_in_fib E ff gg) _ _ _) ;
               rewrite comp_full_sub_disp_cat_fib ;
               apply idpath).
        + abstract
            (intro ξ ;
             use subtypePath ; [ intro ; apply homset_property | ] ;
             use (EqualizerInsEq (equalizer_in_fib E ff gg)) ;
             refine (_ @ !(EqualizerCommutes (equalizer_in_fib E ff gg) _ _ _)) ;
             refine (_ @ pr2 ξ) ;
             rewrite comp_full_sub_disp_cat_fib ;
             apply idpath).
    Defined.

    Definition preserves_equalizer_full_sub_disp_cat_fiber_functor_iso
               {x y : full_subcat C P}
               {f : x --> y}
               {yy₁ yy₂ : full_sub_disp_cat[{y}]}
               {g₁ g₂ : yy₁ --> yy₂}
      : z_iso
          (equalizer_in_fib
             E
             (# (fiber_functor_from_cleaving D HD (pr1 f)) g₁)
             (# (fiber_functor_from_cleaving D HD (pr1 f)) g₂))
          (equalizer_in_fib
             E
             (# (fiber_functor_from_cleaving
                   full_sub_disp_cat
                   (cleaving_full_sub_disp_cat HD HQ)
                   f)
                g₁)
             (# (fiber_functor_from_cleaving
                   full_sub_disp_cat
                   (cleaving_full_sub_disp_cat HD HQ)
                   f)
                g₂)).
    Proof.
      use make_z_iso.
      - use EqualizerIn.
        + apply EqualizerArrow.
        + abstract
            (rewrite !full_sub_disp_cat_fiber_functor_from_cleaving ;
             apply EqualizerEqAr).
      - use EqualizerIn.
        + apply EqualizerArrow.
        + abstract
            (rewrite !full_sub_disp_cat_fiber_functor_from_cleaving ;
             apply EqualizerEqAr).
      - split.
        + abstract
            (use EqualizerInsEq ;
             rewrite !assoc' ;
             rewrite EqualizerCommutes ;
             rewrite id_left ;
          apply EqualizerCommutes).
        + abstract
            (use EqualizerInsEq ;
             rewrite !assoc' ;
             etrans ;
             [ apply maponpaths ;
              apply EqualizerCommutes
             | ] ;
             rewrite EqualizerCommutes ;
             rewrite id_left ;
             apply idpath).
    Defined.

    Proposition preserves_equalizer_full_sub_disp_cat_fiber_functor
                {x y : full_subcat C P}
                (f : x --> y)
      : preserves_equalizer
          (fiber_functor_from_cleaving
             full_sub_disp_cat
             (cleaving_full_sub_disp_cat HD HQ)
             f).
    Proof.
      use preserves_equalizer_if_preserves_chosen.
      {
        apply full_sub_disp_cat_fiber_equalizers.
      }
      intros yy₁ yy₂ g₁ g₂ p.
      use (isEqualizer_z_iso
             (isEqualizer_Equalizer
                (full_sub_disp_cat_fiber_equalizers x _ _ _ _))).
      - use full_sub_disp_cat_fiber_z_iso.
        refine (z_iso_comp
                  (preserves_equalizer_z_iso
                     _
                     (pr2 E (pr1 x) (pr1 y) (pr1 f))
                     (equalizer_in_fib E g₁ g₂)
                     (equalizer_in_fib
                        E
                        _
                        _))
                  _).
        apply preserves_equalizer_full_sub_disp_cat_fiber_functor_iso.
      - cbn -[fiber_category fiber_functor_from_cleaving].
        unfold preserves_equalizer_full_sub_disp_cat_fiber_functor_iso.
        rewrite full_sub_disp_cat_fiber_functor_from_cleaving.
        rewrite comp_full_sub_disp_cat_fib.
        rewrite !assoc'.
        rewrite EqualizerCommutes.
        refine (!_).
        apply (EqualizerCommutes
                 (equalizer_in_fib
                    E
                    (# (fiber_functor_from_cleaving D HD (pr1 f)) g₁)
                    (# (fiber_functor_from_cleaving D HD (pr1 f)) g₂))).
    Qed.

    Definition full_sub_disp_cat_fiberwise_equalizers
      : fiberwise_equalizers (cleaving_full_sub_disp_cat HD HQ).
    Proof.
      split.
      - exact full_sub_disp_cat_fiber_equalizers.
      - intros x y f.
        apply preserves_equalizer_full_sub_disp_cat_fiber_functor.
    Defined.
  End Equalizers.

  (** * 7. Properties of the inclusion *)
  Proposition preserves_terminal_full_subcat_incl
              (T : Terminal C)
              (H : P T)
    : preserves_terminal full_subcat_incl.
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      exact (full_subcat_terminal _ T H).
    }
    exact (pr2 T).
  Qed.

  Proposition is_cartesian_full_sub_disp_cat_incl
              (HD : cleaving D)
              (HQ : ∏ (x y : C)
                      (f : y --> x)
                      (xx : D x)
                      (px : P x)
                      (py : P y)
                      (qxx : Q x px xx),
                    Q y py (HD _ _ f xx))
    : is_cartesian_disp_functor full_sub_disp_cat_incl.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact (cleaving_full_sub_disp_cat HD HQ).
    }
    intros x y f yy.
    cbn.
    exact (HD (pr1 y) (pr1 x) (pr1 f) (pr1 yy)).
  Qed.

  Proposition preserves_terminal_fiber_functor_incl
              (HD : cleaving D)
              (T : fiberwise_terminal HD)
              (HT : ∏ (x : C) (p : P x), Q x p (terminal_obj_in_fib T x))
              (x : full_subcat C P)
    : preserves_terminal (fiber_functor full_sub_disp_cat_incl x).
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      exact (full_sub_disp_cat_fiber_terminal HD T HT x).
    }
    unfold preserves_chosen_terminal.
    cbn.
    apply (pr1 T (pr1 x)).
  Qed.

  Proposition preserves_binproduct_fiber_functor_incl
              (HD : cleaving D)
              (BP : fiberwise_binproducts HD)
              (HBP : ∏ (x : C)
                       (px : P x)
                       (xx₁ xx₂ : D x)
                       (qxx₁ : Q x px xx₁)
                       (qxx₂ : Q x px xx₂),
                     Q x px (BinProductObject _ (binprod_in_fib BP xx₁ xx₂)))
              (x : full_subcat C P)
    : preserves_binproduct (fiber_functor full_sub_disp_cat_incl x).
  Proof.
    use preserves_binproduct_if_preserves_chosen.
    {
      exact (full_sub_disp_cat_fiber_binproducts HD BP HBP x).
    }
    intros xx yy.
    use (isBinProduct_z_iso
           (isBinProduct_BinProduct
              _
              (pr1 BP (pr1 x) (pr1 xx) (pr1 yy)))).
    - apply identity_z_iso.
    - rewrite fiber_functor_full_sub_disp_cat_incl.
      exact (!(id_left _)).
    - rewrite fiber_functor_full_sub_disp_cat_incl.
      exact (!(id_left _)).
  Qed.

  Proposition preserves_equalizer_fiber_functor_incl
              (HD : cleaving D)
              (E : fiberwise_equalizers HD)
              (HE : ∏ (x : C)
                      (px : P x)
                      (xx₁ xx₂ : D x)
                      (qxx₁ : Q x px xx₁)
                      (qxx₂ : Q x px xx₂)
                      (ff gg : xx₁ -->[ identity _ ] xx₂),
                  Q x px (EqualizerObject (equalizer_in_fib E ff gg)))
              (x : full_subcat C P)
    : preserves_equalizer (fiber_functor full_sub_disp_cat_incl x).
  Proof.
    use preserves_equalizer_if_preserves_chosen.
    {
      exact (full_sub_disp_cat_fiber_equalizers HD E HE x).
    }
    intros xx yy g₁ g₂ p.
    use (isEqualizer_z_iso
           (isEqualizer_Equalizer
              (pr1 E (pr1 x) (pr1 xx) (pr1 yy) _ _))).
    - use make_z_iso.
      + use EqualizerIn.
        * apply EqualizerArrow.
        * abstract
            (rewrite !fiber_functor_full_sub_disp_cat_incl ;
             apply EqualizerEqAr).
      + use EqualizerIn.
        * apply EqualizerArrow.
        * abstract
            (rewrite !fiber_functor_full_sub_disp_cat_incl ;
             apply EqualizerEqAr).
      + split.
        * abstract
            (use EqualizerInsEq ;
             rewrite !assoc' ;
             cbn -[fiber_category] ;
             rewrite !EqualizerCommutes ;
             rewrite id_left ;
             apply idpath).
        * abstract
            (use EqualizerInsEq ;
             rewrite !assoc' ;
             cbn -[fiber_category] ;
             rewrite !EqualizerCommutes ;
             rewrite id_left ;
             apply idpath).
    - rewrite fiber_functor_full_sub_disp_cat_incl.
      cbn -[fiber_category].
      rewrite EqualizerCommutes.
      apply idpath.
  Qed.
End FullSubDispCat.
