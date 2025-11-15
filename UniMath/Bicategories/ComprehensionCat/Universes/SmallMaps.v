(**

 Small maps from a universe

 Universes are essential in the context of algebraic set theory where one is interested in
 making models of various flavors of Zermelo-Fraenkel set theory. Developments of algebraic
 set theory usually proceed as follows.
 - One starts with some ambient category `C`. This category is required to satisfy several
   properties, usually that it is finitely complete, extensive, regular, and that it is a
   Heyting category.
 - This category must be equipped with a class of maps, which are called the small maps.
   If we think about small maps from the context of set theory, then we think of them as
   maps `f : x --> y` whose fibers are contained in some fixed cardinal `κ`. There are
   various axiomatizations for the class of small maps, and we discuss them below.
 - There must be a universe. Specifically, there is a morphsm `p : e --> b` such that every
   small map can be obtained as some pullback of `p`.
 - There also must be a powerclass operator, which intuitively means that for every object
   `x` we have an object `P x` that contains all small subobjects of `x` (i.e., all small
   monomorphism into `x`), and this powerclass operator must have an initial algebra.

 The final ingredient (powerclass and its initial algebra) is necessary to construct the
 collection `V` of all sets, which allows us to make models of Zermelo-Fraenkel set theory
 where one has unbounded quantification. However, in this file we are only interested in the
 first three ingredients.

 There are various axioms that one considers for classes of small maps. Here we list some of
 them and we give their type theoretic interpretation.
 - Every identity morphism is small. From a type theoretic perspective, this means that the
   terminal object is small.
 - The composition of small morphisms is small. From a type theoretic perspective, this means
   that small types are closed under ∑-types.
 - Every monomorphism is small. This corresponds to propositional resizing, as it says that
   the universe contains every proposition (monomorphisms correspond to propositions).
 - Small morphisms are closed under pullback. This means that small types are closed under
   substitution.
 - Small morphisms are closed under taking copairs. This means that small types are closed
   under sums.
 - Small morphisms are closed under regular epimorphisms. This means that every quotient of
   a small type again is small. Note that there is no restriction on the equivalence relation,
   which can be large.
 - The natural numbers object and the subobject classifier are small. The first means that the
   type of natural numbers is small and the second is another impredicativity axiom. More
   specifically, it says that the type of all propositions is small.
 And there are much more axioms that one might consider for classes of small maps depending on
 the context.

 In this file, we construct a class of small maps in every category with a universe. We also
 show how closure conditions of the universe gives rise to closure conditions on the class of
 small maps. The main idea is that a morphism is said to be small if there is a code in the
 universe whose associated type corresponds to that type. If we use suggestive notation, then
 we can see a morphism `π A : Γ & A --> Γ` as a type `A` in context `Γ`, and we say that `A` is
 small if there is a term `a` of the universe type in context `Γ` such that `el a` and `A` are
 isomorphic.

 It is worthwhile to notice that approaches based on small maps endow morphisms with an
 additional property. However, our development of type formers is based on operations. More
 concretely, the axiom for ∑-types in the context of small maps says that small maps are closed
 under composition, and this purely talks about property. However, our axiom for ∑-types is
 expressed via an operation on terms of the universe type with suitable stability conditions.

 To illustrate the axioms below, we compare them to "A brief introduction to algebraic set
 theory" by Awodey, and we highlight similarities and differences. Note that the axiom (U),
 which says that the powerclass has an initial algebra `V`, is not considered in this file.

 References
 - "A brief introduction to algebraic set theory" by Awodey
 - "Algebraic set theory" by Joyal and Moerdijk
 - "A unified approach to algebraic set theory" by Van den Berg and Moerdijk
 - "Elementary axioms for categories of classes" by Simpson
 - "Type theories, toposes and constructive set theory: predicative aspects of AST" by Moerdijk
   and Palmgren

 Contents
 1. Small maps
 2. Closure under isomorphism
 3. Closure under pullback
 4. All isomorphisms are small
 5. Composition of small maps
 6. All monomorphisms are small
 7. Copairs are small
 8. Small NNOs
 9. Small subobject classifiers
 10. ∏-types
                                                                                           *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Constant.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Identity.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Resizing.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Sigma.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Sum.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.PiTypes.

Local Open Scope cat.

Section SmallMaps.
  Context {C : univ_cat_with_finlim_universe}.

  Local Notation "𝟙" := (terminal_univ_cat_with_finlim C).

  Let u : C := univ_cat_universe C.
  Let el : cat_stable_el_map_coherent C
    := univ_cat_cat_stable_el_map C.

  (** * 1. Small maps *)
  Definition is_small_map
             {x y : C}
             (f : x --> y)
    : hProp
    := ∃ (a : y --> u)
         (h : z_iso (cat_el_map_el el a) x),
       cat_el_map_mor el a = h · f.

  Definition small_object
             (x : C)
    : hProp
    := is_small_map (TerminalArrow 𝟙 x).

  (** * 2. Closure under isomorphism *)
  Proposition is_small_map_z_iso
              {x x' y : C}
              (f : x --> y)
              (g : x' --> y)
              (h : z_iso x x')
              (p : f = h · g)
              (Hf : is_small_map f)
    : is_small_map g.
  Proof.
    revert Hf.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ a [ k q ]].
    use hinhpr.
    simple refine (a ,, _ ,, _).
    - exact (z_iso_comp k h).
    - simpl.
      rewrite q.
      rewrite p.
      rewrite assoc'.
      apply idpath.
  Qed.

  (** * 3. Closure under pullback *)

  (**
     This corresponds to axiom (S2) in "A brief introduction to algebraic set theory"
     by Awodey
   *)
  Proposition is_small_map_pullback
              {w x y z : C}
              {f : y --> z}
              {g : x --> z}
              {π₁ : w --> x}
              {π₂ : w --> y}
              (p : π₁ · g = π₂ · f)
              (pb : isPullback p)
              (Hg : is_small_map g)
    : is_small_map π₂.
  Proof.
    pose (P := make_Pullback _ pb).
    revert Hg.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros ahq.
    induction ahq as [ a [ h q ]].
    use hinhpr.
    simple refine (f · a ,, _  ,, _).
    - use (iso_between_pullbacks
               _ _
               (isPullback_Pullback (cat_stable_el_map_pb el f a))
               pb).
      + exact h.
      + exact (identity_z_iso _).
      + exact (identity_z_iso _).
      + abstract
          (rewrite id_right ;
           exact (!q)).
      + abstract
          (rewrite id_left, id_right ;
           apply idpath).
    - use z_iso_inv_to_left.
      etrans.
      {
        apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el f a)).
      }
      apply id_right.
  Qed.

  (** * 4. All isomorphisms are small *)
  (**
     The statement `all_identity_small` corresponds to axiom (S1) in "A brief introduction
     to algebraic set theory" by Awodey. Note that our class of small maps is closed under
     isomorphism, because small maps are some pullback of the universe. For this reason,
     we can conclude that all isomorphisms are small.

     Note that (S1) says that the small maps form a subcategory, so they contain all identities
     and they are closed under composition,
   *)
  Proposition terminal_identity_small
              (unit_c : terminal_in_cat_univ C)
    : is_small_map (identity 𝟙).
  Proof.
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (type_in_cat_univ_code unit_c).
    - exact (type_in_cat_univ_z_iso _).
    - simpl.
      apply TerminalArrowEq.
  Qed.

  Proposition all_identity_small
              (unit_c : terminal_in_cat_univ C)
              (x : C)
    : is_small_map (identity x).
  Proof.
    simple refine (is_small_map_pullback _ _ (terminal_identity_small unit_c)).
    - apply TerminalArrow.
    - apply TerminalArrow.
    - apply TerminalArrowEq.
    - intros w h k q.
      use iscontraprop1.
      + use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        refine (_ @ pr22 ζ₁ @ !(pr22 ζ₂) @ _).
        * exact (!(id_right _)).
        * apply id_right.
      + refine (k ,, _ ,, _).
        * apply TerminalArrowEq.
        * apply id_right.
  Qed.

  Proposition all_isos_small
              (unit_c : terminal_in_cat_univ C)
              {x : C}
              (f : z_iso x x)
    : is_small_map f.
  Proof.
    simple refine (is_small_map_z_iso _ _ _ _ (all_identity_small unit_c x)).
    - exact (z_iso_inv f).
    - exact (!(z_iso_after_z_iso_inv f)).
  Qed.

  (** * 5. Composition of small maps *)
  (**
     This corresponds to axiom (S1) in "A brief introduction to algebraic set theory" by Awodey.

     Note that (S1) says that the small maps form a subcategory, so they contain all identities
     and they are closed under composition,
   *)
  Proposition all_composition_small
              (sig : cat_univ_stable_codes_sigma C)
              {x y z : C}
              {f : x --> y}
              {g : y --> z}
              (Hf : is_small_map f)
              (Hg : is_small_map g)
    : is_small_map (f · g).
  Proof.
    revert Hg.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ a [ hg qg ]].
    revert Hf.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ b [ hf qf ]].
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (cat_univ_codes_sigma_ty sig a (hg · b)).
    - refine (z_iso_comp
                (cat_univ_codes_sigma_iso sig a (hg · b))
                _).
      refine (z_iso_comp _ hf).
      apply cat_el_map_pb_mor_z_iso.
    - simpl.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        exact (!qf).
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        exact (PullbackSqrCommutes (cat_stable_el_map_pb el hg b)).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (!qg).
      }
      rewrite !assoc.
      refine (!_).
      apply cat_univ_codes_sigma_comm.
  Qed.

  (** * 6. All monomorphisms are small *)
  (**
     This corresponds to axiom (S3) in "A brief introduction to algebraic set theory" by Awodey.
   *)
  Proposition all_monics_small
              (resize : cat_univ_stable_codes_resizing C)
              {x y : C}
              (m : Monic C x y)
    : is_small_map m.
  Proof.
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (cat_univ_resize_monic resize m).
    - exact (cat_univ_resize_z_iso resize m).
    - refine (!_).
      exact (cat_univ_resize_z_iso_comm resize m).
  Qed.

  (** * 7. Copairs are small *)
  (**
     This corresponds to axiom (S5) in "A brief introduction to algebraic set theory" by Awodey.
   *)
  Proposition small_copairs
              {BC : BinCoproducts C}
              (sum : cat_univ_stable_codes_sums BC)
              {x y z : C}
              {f : x --> z}
              {g : y --> z}
              (Hf : is_small_map f)
              (Hg : is_small_map g)
    : is_small_map (BinCoproductArrow (BC x y) f g).
  Proof.
    revert Hf.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ a [ hf qf ]].
    revert Hg.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ b [ hg qg ]].
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (cat_univ_codes_sums_sum sum a b).
    - exact (z_iso_comp
               (z_iso_inv (cat_univ_codes_sums_z_iso sum a b))
               (bincoproduct_of_z_iso _ _ hf hg)).
    - simpl.
      rewrite !assoc'.
      refine (!_).
      use z_iso_inv_on_right.
      refine (_ @ cat_univ_codes_sums_sum_comm _ _ _).
      exact (precompWithBinCoproductArrow_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ qf qg).
  Qed.

  (** * 8. Small NNOs *)
  (**
     This corresponds to axiom (I) in "A brief introduction to algebraic set theory" by Awodey.
   *)
  Proposition nno_small
              {N : parameterized_NNO 𝟙 (binproducts_univ_cat_with_finlim C)}
              (N_c : pnno_in_cat_univ N)
    : small_object N.
  Proof.
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (type_in_cat_univ_code N_c).
    - exact (type_in_cat_univ_z_iso _).
    - apply TerminalArrowEq.
  Qed.

  (** * 9. Small subobject classifiers *)
  (**
     Axiom (P1) and (P2) in "A brief introduction to algebraic set theory" by Awodey says
     that powerclasses exist and that powerclasses of small objects again are small objects.
     From this, one can conclude that the ambient category has a subobject classifier (see
     Proposition 2.5 in "Elementary axioms for categories of classes" by Simpson), and that
     the subobject classifier is small. Note that here one needs that all monomorphisms are
     small. The following statement expresses the smallness of the subobject classifier.

     If the ambient category is locally Cartesian closed, then powerclasses can be constructed
     from the subobject classifier.
   *)
  Proposition subobject_classifier_small
              {Ω : subobject_classifier 𝟙}
              (Ω_c : subobject_classifier_in_cat_univ Ω)
    : small_object Ω.
  Proof.
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (type_in_cat_univ_code Ω_c).
    - exact (type_in_cat_univ_z_iso _).
    - apply TerminalArrowEq.
  Qed.

  (** * 10. ∏-types *)
  Section HelpIso.
    Context {Γ : C}
            {πA : C/Γ}
            {a : Γ --> u}
            (hg : z_iso (cat_el_map_el el a) (cod_dom πA))
            (b : cod_dom πA --> u).

    Definition pi_types_small_pb_iso_mor
      : pullbacks_univ_cat_with_finlim
          C
          (cat_el_map_el el a)
          (cat_el_map_el (univ_cat_cat_stable_el_map C) (hg · b)) (cod_dom πA)
          (cat_el_map_mor (univ_cat_cat_stable_el_map C) (hg · b)) (inv_from_z_iso hg)
         -->
         cat_el_map_el el (hg · b).
    Proof.
      use (PullbackArrow (cat_stable_el_map_pb el hg b)).
      - exact (PullbackPr1 _ · cat_el_map_pb_mor_z_iso el hg b).
      - exact (PullbackPr2 _ · inv_from_z_iso hg).
      - abstract
          (simpl ;
           rewrite !assoc' ;
           refine (maponpaths (λ z, _ · z) (cat_el_map_pb_mor_comm el hg b) @ _) ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply PullbackSqrCommutes).
    Defined.

    Definition pi_types_small_pb_iso_inv
      : cat_el_map_el el (hg · b)
        -->
        pullbacks_univ_cat_with_finlim
          C
          (cat_el_map_el el a)
          (cat_el_map_el (univ_cat_cat_stable_el_map C) (hg · b)) (cod_dom πA)
          (cat_el_map_mor (univ_cat_cat_stable_el_map C) (hg · b)) (inv_from_z_iso hg).
    Proof.
      use PullbackArrow.
      - apply identity.
      - exact (cat_el_map_mor el _ · hg).
      - abstract
          (rewrite id_left ;
           use z_iso_inv_on_left ;
           apply idpath).
    Defined.

    Proposition pi_types_small_pb_iso_laws
      : is_inverse_in_precat
          pi_types_small_pb_iso_mor
          pi_types_small_pb_iso_inv.
    Proof.
      unfold pi_types_small_pb_iso_mor, pi_types_small_pb_iso_inv.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left, id_right.
          use (MorphismsIntoPullbackEqual
                 (isPullback_Pullback (cat_stable_el_map_pb el hg b))).
          * rewrite PullbackArrow_PullbackPr1 ; simpl.
            apply idpath.
          * rewrite PullbackArrow_PullbackPr2 ; simpl.
            refine (!_).
            apply PullbackSqrCommutes.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el hg b)).
          }
          rewrite !assoc'.
          rewrite z_iso_after_z_iso_inv.
          apply id_right.
      - use (MorphismsIntoPullbackEqual
               (isPullback_Pullback (cat_stable_el_map_pb el hg b))).
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el hg b)).
          }
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el hg b)).
          }
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          refine (!_).
          use z_iso_inv_on_left.
          apply idpath.
    Qed.

    Definition pi_types_small_pb_iso
      : z_iso
          (pullbacks_univ_cat_with_finlim
             C
             (cat_el_map_el el a)
             (cat_el_map_el (univ_cat_cat_stable_el_map C) (hg · b)) (cod_dom πA)
             (cat_el_map_mor (univ_cat_cat_stable_el_map C) (hg · b)) (inv_from_z_iso hg))
          (cat_el_map_el el (hg · b)).
    Proof.
      use make_z_iso.
      - exact pi_types_small_pb_iso_mor.
      - exact pi_types_small_pb_iso_inv.
      - exact pi_types_small_pb_iso_laws.
    Defined.

    Definition pi_types_small_iso
      : z_iso
          (cod_pb
             (pullbacks_univ_cat_with_finlim C)
             (z_iso_inv hg)
             (cat_el_map_slice
                (univ_cat_cat_stable_el_map C)
                (hg · b)))
          (cat_el_map_slice el b).
    Proof.
      use make_z_iso_in_slice.
      - exact (z_iso_comp
                 pi_types_small_pb_iso
                 (cat_el_map_pb_mor_z_iso el hg b)).
      - abstract
          (simpl ;
           rewrite !assoc' ;
           etrans ;
           [ apply maponpaths ;
             apply (cat_el_map_pb_mor_comm el hg b)
           | ] ;
           rewrite !assoc ;
           etrans ;
           [ apply maponpaths_2 ;
             apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el hg b))
           | ] ;
           rewrite !assoc' ;
           rewrite z_iso_after_z_iso_inv ;
           apply id_right).
    Defined.
  End HelpIso.

  Proposition pi_types_small
              {HC : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim C)}
              (Π : cat_univ_stable_codes_pi HC)
              {Γ : C}
              {πA : C/Γ}
              {πB : C/cod_dom πA}
              (HA : is_small_map (cod_mor πA))
              (HB : is_small_map (cod_mor πB))
    : is_small_map (cod_mor (lccc_exp_fib HC πA πB)).
  Proof.
    revert HA.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ a [ hg qg ]].
    revert HB.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros [ b [ hf qf ]].
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact (cat_univ_codes_pi_ty Π a (hg · b)).
    - refine (z_iso_comp _ _).
      + exact (z_iso_to_cod_dom _ _ _ (cat_univ_codes_pi_iso_slice Π a (hg · b))).
      + use lccc_exp_functor_z_iso.
        * exact (z_iso_inv hg).
        * abstract
            (refine (!_) ;
             use z_iso_inv_on_right ;
             exact qg).
        * exact (z_iso_comp
                   (pi_types_small_iso hg b)
                   (make_z_iso_in_slice _ _ _ hf (!qf))).
    - simpl.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply mor_eq.
      }
      apply mor_eq.
  Qed.
End SmallMaps.
