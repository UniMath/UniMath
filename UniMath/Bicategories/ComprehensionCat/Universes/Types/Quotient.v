(**


 Contents
 1. Equivalence relations internal to a universe
 2. Codes for quotient types

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.SliceInternalEqRel.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRegular.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.

Local Open Scope cat.

(*
  Strategy for quotient types

  Codes for quotients in compcat:
  - we have ctx Γ
  - we have type A in Γ
  - we have a type R in Γ . A . A [ π ]
  - R is an hProp
  - R is reflexive, symmetric and transitive
  - we express reflexivity as:
       for all Δ
       for all Δ ⊢ t : A
       we have R t t
  - similar ideas for symmetric and transitive
  - we must show that this gives rise to a quotient
    ~> this gives rise to an internal equivalence relation in slices

 For quotients in a category: we express the same, but for categories instead
    ~> using the slice category

 So: for quotient in category
    ~> we must show that this data gives rise to an internal eqrel in the slice

 This is fine for quotient types in comprehension categories

 --------------------------------------
 For quotient types in categories:
   ~> if A in U
      we have a regular epi A --> B
      then B in U

 This is what they do in algebraic set theory
 and this is just much simpler

 It also prevents duplication

 However, this approach has a drawback.
 Because we assume that the category is exact (rather than bounded exact), all quotients exist,
 including quotients by unbounded equivalence relations.
 Let's look at an example. Let φ be a proposition and define the following equivalence relation
 on 1+1:
    inl tt ~ inr tt iff φ
 Now we can form 1+1/~ and we have a regular epi `1+1 --> 1+1/~`
 Since 1+1 is small, so is 1+1/~ and thus equality of 1+1/~ is small as well.
 However, by effectiveness this means that ~ is a small equivalence relation, and thus φ must
 be small. Hence, unbounded small quotients imply a certain amount of impredicavity. For this
 reason, one must choose between one of the following:
 - all quotients must be bounded (this is chosen by Van den Berg&Moerdijk)
 - quotients only are small if the equivalence relation is small
 The second approach fits better if one assume exactness and allows for all quotients.

 We can also look at a concrete example, namely Set₁. We have a universe in Set₁ given by the
 iterative sets in Set₀. Now let X be an interative set in Set₀ and let R be an equivalence
 relation on X valued in Set₁. We can still form the quotient, which still is an iterative
 set. However, the resulting quotient lives in Set₁, and, in general, not in Set₀ (unless one
 assume impredicativity).

 Another possible solution is the following: restrict B to locally small types (i.e., types for
 which the identity type relation is small). This axiom is uglier and more indirect to formulate
 in this setting.

 *)


Definition le_koe
           {C : category}
           (HC : is_exact C)
           (PB : Pullbacks C)
           {Γ Δ A : C}
           {π : A --> Δ}
           (r : internal_type_eqrel PB π)
           (s : Γ --> Δ)
  : UU.
Proof.
  pose (P := PB _ _ _ s π).
  pose (src := PB _ _ _ (PullbackPr2 P) (dom_mor (internal_type_rel_to_slice_rel_src PB π r))).
  assert (src --> P) as tar.
  {
    use PullbackArrow.
    - refine (PullbackPr1 _ · PullbackPr1 _).
    - refine (PullbackPr2 _ · dom_mor (internal_type_rel_to_slice_rel_tar PB π r)).
    - cbn.
      rewrite !assoc'.
      rewrite <- PullbackSqrCommutes.
      unfold src.
      cbn.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        refine (!_).
        apply PullbackSqrCommutes.
      }
      rewrite !assoc'.

      cbn.
      unfold P.
      rewrite PullbackSqrCommutes.
      apply idpath.
  }
  (*
    Claim: P is the coequalizer of src and tar
   *)


Admitted.



Definition mor_from_quot_internal_type_eqrel
           {C : category}
           (HC : is_exact C)
           (PB : Pullbacks C)
           {Γ A : C}
           {π : A --> Γ}
           (r : internal_type_eqrel PB π)
           {B : C}
           (f : A --> B)
           (p : PullbackPr1
    (PB (cod_dom (quot_internal_type_eqrel HC PB r)) A A
       (dom_mor (CoequalizerArrow (quot_internal_type_eqrel HC PB r)))
       (dom_mor (CoequalizerArrow (quot_internal_type_eqrel HC PB r))))
  · f =
  PullbackPr2
    (PB (cod_dom (quot_internal_type_eqrel HC PB r)) A A
       (dom_mor (CoequalizerArrow (quot_internal_type_eqrel HC PB r)))
       (dom_mor (CoequalizerArrow (quot_internal_type_eqrel HC PB r))))
  · f)
  : cod_dom (quot_internal_type_eqrel HC PB r) --> B.
Proof.
  pose (make_Coequalizer
          _ _ _ _
          (regular_epi_coeq_kernel_pair
             PB
             (from_regular_epi_in_slice
                PB
                (is_regular_category_coeqs_of_kernel_pair HC)
                (is_regular_category_regular_epi_pb_stable HC)
                (is_regular_epi_quot_internal_type_eqrel HC PB r))))
    as Coeq.
  use (CoequalizerOut Coeq).
  - exact f.
  - cbn.
    cbn.
Admitted.


Definition quot_internal_type_eqrel_functor
           {C : category}
           (HC : is_exact C)
           (PB : Pullbacks C)
           {Γ Δ A B : C}
           (s : Γ --> Δ)
           {πA : A --> Δ}
           (rA : internal_type_eqrel PB πA)
           {πB : B --> Γ}
           (rB : internal_type_eqrel PB πB)
           (f : A --> B)
           (p : f · πB · s = πA)
           (q : internal_type_rel_monic rA · PullbackPr1 (PB Δ A A πA πA)
  · (f · dom_mor (CoequalizerArrow (quot_internal_type_eqrel HC PB rB))) =
  internal_type_rel_monic rA · PullbackPr2 (PB Δ A A πA πA)
  · (f · dom_mor (CoequalizerArrow (quot_internal_type_eqrel HC PB rB))))
  : cod_dom (quot_internal_type_eqrel HC PB rA)
    -->
    cod_dom (quot_internal_type_eqrel HC PB rB).
Proof.
  use (dom_mor
         (CoequalizerOut
            (quot_internal_type_eqrel HC PB rA)
            (make_cod_fib_ob _)
            _
            _)).
  - exact (pr211 (quot_internal_type_eqrel HC PB rB) · s).
  - use make_cod_fib_mor.
    + refine (_ · dom_mor (CoequalizerArrow _)).
      exact f.
    + cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        exact (mor_eq (CoequalizerArrow (quot_internal_type_eqrel HC PB rB))).
      }
      cbn.
      rewrite !assoc.
      exact p.
  - use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    cbn.
    exact q.
Defined.

Definition cat_el_map_mor_subst_monic
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map_coherent C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           {a : Δ --> univ_cat_universe C}
           (Ha : isMonic (cat_el_map_mor el a))
  : isMonic (cat_el_map_mor el (s · a)).
Proof.
  exact (MonicPullbackisMonic _ (make_Monic _ _ Ha) s (cat_stable_el_map_pb el s a)).
Defined.


Section TruncInCatWithUniv.
  Context {C : univ_cat_with_finlim_ob}
          {HC : is_exact C}
          {el : cat_stable_el_map_coherent C}.

  Let PB : Pullbacks C := pullbacks_univ_cat_with_finlim C.

  (** * 1. Equivalence relations internal to a universe *)
  Definition univ_internal_rel
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
    : UU
    := ∑ (r : PB _ _ _ (cat_el_map_mor el a) (cat_el_map_mor el a)
              -->
              univ_cat_universe C),
       isMonic (cat_el_map_mor el r).

  Coercion univ_internal_rel_to_code
           {Γ : C}
           {a : Γ --> univ_cat_universe C}
           (r : univ_internal_rel a)
    : PB _ _ _ (cat_el_map_mor el a) (cat_el_map_mor el a)
      -->
      univ_cat_universe C
    := pr1 r.

  Proposition is_monic_univ_internal_rel
              {Γ : C}
              {a : Γ --> univ_cat_universe C}
              (r : univ_internal_rel a)
    : isMonic (cat_el_map_mor el r).
  Proof.
    exact (pr2 r).
  Defined.

  Definition univ_internal_rel_to_monic
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_rel a)
    : Monic _ (cat_el_map_el el r) (PB _ _ _ (cat_el_map_mor el a) (cat_el_map_mor el a)).
  Proof.
    use make_Monic.
    - exact (cat_el_map_mor el r).
    - exact (is_monic_univ_internal_rel r).
  Defined.

  Definition make_univ_internal_rel
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : PB _ _ _ (cat_el_map_mor el a) (cat_el_map_mor el a)
                  -->
                  univ_cat_universe C)
             (Hr : isMonic (cat_el_map_mor el r))
    : univ_internal_rel a
    := r ,, Hr.

  Definition univ_internal_rel_to_type_rel
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_rel a)
    : internal_type_rel PB (cat_el_map_mor el a).
  Proof.
    use make_internal_type_rel.
    - exact (cat_el_map_el el r).
    - exact (univ_internal_rel_to_monic r).
  Defined.

  Definition univ_internal_rel_iseqrel
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_rel a)
    : UU
    := internal_type_rel_iseqrel (univ_internal_rel_to_type_rel r).

  Definition univ_internal_eqrel
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
    : UU
    := ∑ (r : univ_internal_rel a),
       univ_internal_rel_iseqrel r.

  Coercion univ_internal_eqrel_to_rel
           {Γ : C}
           {a : Γ --> univ_cat_universe C}
           (r : univ_internal_eqrel a)
    : univ_internal_rel a
    := pr1 r.

  Proposition univ_internal_eqrel_iseqrel
              {Γ : C}
              {a : Γ --> univ_cat_universe C}
              (r : univ_internal_eqrel a)
    : univ_internal_rel_iseqrel r.
  Proof.
    exact (pr2 r).
  Defined.

  Definition make_univ_internal_eqrel
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_rel a)
             (Hr : univ_internal_rel_iseqrel r)
    : univ_internal_eqrel a
    := r ,, Hr.

  Definition univ_internal_rel_to_type_eqrel
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_eqrel a)
    : internal_type_eqrel PB (cat_el_map_mor el a).
  Proof.
    use make_internal_type_eqrel.
    - exact (univ_internal_rel_to_type_rel r).
    - exact (univ_internal_eqrel_iseqrel r).
  Defined.

  (** * 2. Substitution for equivalence relations internal to a universe *)
  Section SubstInternalRelUniv.
    Context {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            {a : Γ₂ --> univ_cat_universe C}.

    Definition subst_univ_internal_rel_mor
               (r : univ_internal_rel a)
      : PB _ _ _ (cat_el_map_mor el (s · a)) (cat_el_map_mor el (s · a))
        -->
        univ_cat_universe C.
    Proof.
      refine (_ · r).
      use PullbackArrow.
      - exact (PullbackPr1 _ · cat_el_map_pb_mor el s a).
      - exact (PullbackPr2 _ · cat_el_map_pb_mor el s a).
      - abstract
          (rewrite !assoc' ;
           rewrite !cat_el_map_pb_mor_comm ;
           rewrite !assoc ;
           rewrite PullbackSqrCommutes ;
           apply idpath).
    Defined.

    Definition subst_univ_internal_rel
               (r : univ_internal_rel a)
      : univ_internal_rel (s · a).
    Proof.
      use make_univ_internal_rel.
      - exact (subst_univ_internal_rel_mor r).
      - abstract
          (use cat_el_map_mor_subst_monic ;
           apply is_monic_univ_internal_rel).
    Defined.

    Definition from_subst_univ_internal_rel_tm
               {Δ : C}
               {s' : Δ --> Γ₁}
               (t : section_of_mor
                      (PullbackPr2 (PB _ _ _ (cat_el_map_mor el (s · a)) s')))
      : section_of_mor (PullbackPr2 (PB _ _ _ (cat_el_map_mor el a) (s' · s))).
    Proof.
      use make_section_of_mor.
      - refine (t · _).
        use PullbackArrow.
        + exact (PullbackPr1 _ · cat_el_map_pb_mor _ _ _).
        + exact (PullbackPr2 _).
        + abstract
            (rewrite !assoc' ;
             rewrite cat_el_map_pb_mor_comm ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             rewrite PullbackSqrCommutes ;
             apply idpath).
      - abstract
          (refine (assoc' _ _ _ @ _ @ section_of_mor_eq t) ;
           apply maponpaths ;
           apply PullbackArrow_PullbackPr2).
    Defined.

    Section FromSubstPrf.
      Context (r : univ_internal_rel a)
              {Δ : C}
              {s' : Δ --> Γ₁}
              {t₁ t₂ : section_of_mor
                         (PullbackPr2 (PB _ _ _ (cat_el_map_mor el (s · a)) s'))}
              (p : internal_type_rel_prf
                     (univ_internal_rel_to_type_rel (subst_univ_internal_rel r))
                     t₁ t₂).

      Proposition from_subst_univ_internal_rel_prf_mor_eq
        : p
          · (PullbackPr1 _
          · cat_el_map_pb_mor
              el
              (PullbackArrow
                 (PB _ _ _ (cat_el_map_mor el a) (cat_el_map_mor el a))
                 (PB _ _ _ (cat_el_map_mor el (s · a)) (cat_el_map_mor el (s · a)))
                 (PullbackPr1 _ · cat_el_map_pb_mor el s a)
                 (PullbackPr2 _ · cat_el_map_pb_mor el s a)
                 _)
              r)
          · internal_type_rel_monic (univ_internal_rel_to_type_rel r)
          =
          identity _
          · subst_rel
              (from_subst_univ_internal_rel_tm t₁)
              (from_subst_univ_internal_rel_tm t₂).
      Proof.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        - rewrite id_left.
          unfold internal_type_rel_monic, subst_rel ; cbn.
          rewrite assoc'.
          rewrite PullbackArrow_PullbackPr1.
          refine (_ @ assoc _ _ _).
          rewrite PullbackArrow_PullbackPr1.
          etrans.
          {
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            apply cat_el_map_pb_mor_comm.
          }
          etrans.
          {
            do 2 apply maponpaths.
            refine (assoc' _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr1.
            apply idpath.
          }
          etrans.
          {
            apply maponpaths.
            do 2 refine (assoc _ _ _ @ _).
            do 2 apply maponpaths_2.
            apply PullbackSqrCommutes.
          }
          etrans.
          {
            apply maponpaths.
            do 2 refine (assoc' _ _ _ @ _).
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr1.
            apply idpath.
          }
          rewrite !assoc.
          etrans.
          {
            do 3 apply maponpaths_2.
            apply section_of_mor_eq.
          }
          rewrite id_left.
          apply idpath.
        - rewrite id_left.
          unfold internal_type_rel_monic, subst_rel ; cbn.
          rewrite assoc'.
          rewrite PullbackArrow_PullbackPr2.
          refine (_ @ assoc _ _ _).
          rewrite PullbackArrow_PullbackPr1.
          etrans.
          {
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            apply cat_el_map_pb_mor_comm.
          }
          etrans.
          {
            do 2 apply maponpaths.
            refine (assoc' _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr2.
            apply idpath.
          }
          etrans.
          {
            apply maponpaths.
            do 2 refine (assoc _ _ _ @ _).
            do 2 apply maponpaths_2.
            apply PullbackSqrCommutes.
          }
          etrans.
          {
            apply maponpaths.
            do 2 refine (assoc' _ _ _ @ _).
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr2.
            apply idpath.
          }
          rewrite !assoc.
          etrans.
          {
            do 3 apply maponpaths_2.
            apply section_of_mor_eq.
          }
          rewrite id_left.
          apply idpath.
      Qed.

      Definition from_subst_univ_internal_rel_prf_mor
        : Δ
          -->
          PB _ _ _
             (internal_type_rel_monic (univ_internal_rel_to_type_rel r))
             (subst_rel
                (from_subst_univ_internal_rel_tm t₁)
                (from_subst_univ_internal_rel_tm t₂)).
      Proof.
        use PullbackArrow.
        - refine (p · _).
          refine (PullbackPr1 _ · _).
          apply cat_el_map_pb_mor.
        - apply identity.
        - exact from_subst_univ_internal_rel_prf_mor_eq.
      Defined.

      Proposition from_subst_univ_internal_rel_prf
        : internal_type_rel_prf
            (univ_internal_rel_to_type_rel r)
            (from_subst_univ_internal_rel_tm t₁)
            (from_subst_univ_internal_rel_tm t₂).
      Proof.
        use make_section_of_mor.
        - exact from_subst_univ_internal_rel_prf_mor.
        - apply PullbackArrow_PullbackPr2.
      Defined.
    End FromSubstPrf.

    Section ToSubstPrf.
      Context (r : univ_internal_rel a)
              {Δ : C}
              {s' : Δ --> Γ₁}
              {t₁ t₂ : section_of_mor
                         (PullbackPr2 (PB _ _ _ (cat_el_map_mor el (s · a)) s'))}
              (p : internal_type_rel_prf
                     (univ_internal_rel_to_type_rel r)
                     (from_subst_univ_internal_rel_tm t₁)
                     (from_subst_univ_internal_rel_tm t₂)).

      Definition to_subst_univ_internal_rel_prf_mor_1
        : Δ
          -->
          PB _ _ _ (cat_el_map_mor el (s · a)) (cat_el_map_mor el (s · a)).
      Proof.
        use PullbackArrow.
        - exact (t₁ · PullbackPr1 _).
        - exact (t₂ · PullbackPr1 _).
        - abstract
            (rewrite !assoc' ;
             rewrite !PullbackSqrCommutes ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             refine (section_of_mor_eq _ @ !(section_of_mor_eq _))).
      Defined.

      Proposition to_subst_univ_internal_rel_prf_mor_2_eq
                  q
        : pr1 p
          · PullbackPr1 _
          · cat_el_map_mor (pr1 el) r
          =
          to_subst_univ_internal_rel_prf_mor_1
          · PullbackArrow
              (PB _ _ _ (cat_el_map_mor el a) (cat_el_map_mor el a))
              (PB _ _ _ (cat_el_map_mor el (s · a))
                 (cat_el_map_mor el (s · a)))
              (PullbackPr1 _ · cat_el_map_pb_mor el s a)
              (PullbackPr2 _ · cat_el_map_pb_mor el s a)
              q.
      Proof.
        unfold to_subst_univ_internal_rel_prf_mor_1.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        - rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc'.
          rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
          rewrite PullbackSqrCommutes.
          rewrite !assoc'.
          unfold subst_rel.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (section_of_mor_eq p).
          }
          rewrite id_left.
          cbn.
          rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          apply idpath.
        - rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr2.
          rewrite !assoc'.
          rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
          rewrite PullbackSqrCommutes.
          rewrite !assoc'.
          unfold subst_rel.
          rewrite PullbackArrow_PullbackPr2.
          rewrite !assoc.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (section_of_mor_eq p).
          }
          rewrite id_left.
          cbn.
          rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          apply idpath.
      Qed.

      Definition to_subst_univ_internal_rel_prf_mor_2
        : Δ --> univ_internal_rel_to_type_rel (subst_univ_internal_rel r).
      Proof.
        use (PullbackArrow (cat_stable_el_map_pb _ _ _)).
        - refine (pr1 p · _).
          refine (PullbackPr1 _).
        - exact to_subst_univ_internal_rel_prf_mor_1.
        - apply to_subst_univ_internal_rel_prf_mor_2_eq.
      Defined.

      Proposition to_subst_univ_internal_rel_prf_eq
        : to_subst_univ_internal_rel_prf_mor_2
          · internal_type_rel_monic
              (univ_internal_rel_to_type_rel
                 (subst_univ_internal_rel r))
          =
          identity _ · subst_rel t₁ t₂.
      Proof.
        rewrite id_left.
        unfold subst_rel, internal_type_rel_monic.
        cbn.
        etrans.
        {
          apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb (pr1 el) _ _)).
        }
        unfold to_subst_univ_internal_rel_prf_mor_1.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        - rewrite !PullbackArrow_PullbackPr1.
          apply idpath.
        - rewrite !PullbackArrow_PullbackPr2.
          apply idpath.
      Qed.

      Proposition to_subst_univ_internal_rel_prf
        : internal_type_rel_prf
            (univ_internal_rel_to_type_rel (subst_univ_internal_rel r))
            t₁ t₂.
      Proof.
        use make_section_of_mor.
        - use PullbackArrow.
          + exact to_subst_univ_internal_rel_prf_mor_2.
          + apply identity.
          + apply to_subst_univ_internal_rel_prf_eq.
        - apply PullbackArrow_PullbackPr2.
      Defined.
    End ToSubstPrf.

    Definition subst_univ_internal_rel_iseqrel
               (r : univ_internal_rel a)
               (Hr : univ_internal_rel_iseqrel r)
      : univ_internal_rel_iseqrel (subst_univ_internal_rel r).
    Proof.
      repeat split.
      - intros Δ s' t.
        use to_subst_univ_internal_rel_prf.
        apply Hr.
      - intros Δ s' t₁ t₂ p.
        use to_subst_univ_internal_rel_prf.
        apply Hr.
        apply from_subst_univ_internal_rel_prf.
        exact p.
      - intros Δ s' t₁ t₂ t₃ p q.
        use to_subst_univ_internal_rel_prf.
        use (pr22 Hr).
        + exact (from_subst_univ_internal_rel_tm t₂).
        + use from_subst_univ_internal_rel_prf.
          exact p.
        + use from_subst_univ_internal_rel_prf.
          exact q.
    Qed.

    Definition subst_univ_internal_eqrel
               (r : univ_internal_eqrel a)
      : univ_internal_eqrel (s · a).
    Proof.
      use make_univ_internal_eqrel.
      - exact (subst_univ_internal_rel r).
      - use subst_univ_internal_rel_iseqrel.
        apply r.
    Defined.
  End SubstInternalRelUniv.

  (** * 2. Codes for quotient types *)
  Definition cat_univ_codes_quot
    : UU
    := ∏ (Γ : C)
         (a : Γ --> univ_cat_universe C)
         (r : univ_internal_eqrel a),
       ∑ (q : Γ --> univ_cat_universe C),
       z_iso
         (cat_el_map_slice el q)
         (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r)).

  Proposition isaset_cat_univ_codes_quot
    : isaset cat_univ_codes_quot.
  Proof.
    use impred_isaset ; intros Γ.
    use impred_isaset ; intros a.
    use impred_isaset ; intros r.
    use isaset_total2.
    - apply homset_property.
    - intros ta.
      apply isaset_z_iso.
  Qed.

  Definition cat_univ_quot_code
             (quot : cat_univ_codes_quot)
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_eqrel a)
    : Γ --> univ_cat_universe C
    := pr1 (quot Γ a r).

  Definition cat_univ_quot_z_iso
             (quot : cat_univ_codes_quot)
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (r : univ_internal_eqrel a)
    : z_iso
        (cat_el_map_slice el (cat_univ_quot_code quot r))
        (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r))
    := pr2 (quot Γ a r).

  Proposition cat_univ_codes_quot_eq
              {quot₁ quot₂ : cat_univ_codes_quot}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (r : univ_internal_eqrel a),
                   cat_univ_quot_code quot₁ r
                   =
                   cat_univ_quot_code quot₂ r)
              (q : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (r : univ_internal_eqrel a),
                  cat_el_map_el_eq el (!(p Γ a r)) · dom_mor (cat_univ_quot_z_iso quot₁ r)
                  =
                  dom_mor (cat_univ_quot_z_iso quot₂ r))
    : quot₁ = quot₂.
  Proof.
    use funextsec ; intro Γ.
    use funextsec ; intro a.
    use funextsec ; intro r.
    use total2_paths_f.
    - exact (p Γ a r).
    - use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : cat_el_map_slice el x --> _), is_z_isomorphism _)).
      }
      use eq_mor_cod_fib.
      unfold dom_mor ; simpl.
      rewrite pr1_transportf.
      rewrite transportf_cat_el_map_el.
      exact (q Γ a r).
  Qed.

  (** * 2. Stability *)

  (*
    el(q_{X,R})[s]
    el(q_{X,R}[s])
    el(q_{X[s],R[s]})
    X[s]/R[s]

    el(q_{X,R})[s]
    (X/R)[s]
    X[s]/R[s]

    Missing aspect:
            (X/R)[s] = X[s]/R[s]

    So:
        we need that X[s]/R[s] is a pullback of s and X/R

    Here we need that PB preserves regular epimorphisms
         X/R --> X is a regular epimorphism
         so: (X/R)[s] --> X[s] is a regular epimorphism
         so: it is a coequalizer

    We must show
       (X/R)[s] = X[s]/R[s]
    via ump of coequalizer

   *)
  Definition is_stable_cat_univ_quot
             (quot : cat_univ_codes_quot)
    : UU.
  Proof.
    refine (∏ (Γ Δ : C)
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
              (r : univ_internal_eqrel a),
            ∑ (p : s · cat_univ_quot_code quot r
                   =
                   cat_univ_quot_code quot (subst_univ_internal_eqrel s r)),
             cat_el_map_pb_mor _ _ _
             · dom_mor (cat_univ_quot_z_iso quot r)
             =
             cat_el_map_el_eq el p
             · dom_mor (cat_univ_quot_z_iso quot (subst_univ_internal_eqrel s r))
             · _).
    assert (cod_dom (quot_internal_type_eqrel
                         HC PB
                         (univ_internal_rel_to_type_eqrel
                            (subst_univ_internal_eqrel s r)))
              -->
              PB _ _ _ s (pr211 (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r)))).
    {
      use (dom_mor (CoequalizerOut _ (make_cod_fib_ob _) _ _)).
      - exact (PullbackPr1 _).
      - use make_cod_fib_mor.
        + cbn.
          use PullbackArrow.
          * refine (cat_el_map_mor _ _).
          * refine (_ · dom_mor (CoequalizerArrow _)).
            apply cat_el_map_pb_mor.
          * (*cbn.
            pose (maponpaths dom_mor (CoequalizerEqAr (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r))))
              as q.
            rewrite !comp_in_cod_fib in q.
            cbn in q.
            rewrite <- cat_el_map_pb_mor_comm.
            rewrite !assoc'.
            apply maponpaths.
            refine (!_).
            apply mor_eq.
             *)
            admit.
        + apply PullbackArrow_PullbackPr1.
      - use eq_mor_cod_fib.
        rewrite !comp_in_cod_fib.
        cbn.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          etrans.
          {
            apply maponpaths.
            apply PullbackSqrCommutes.
          }
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          pose (maponpaths dom_mor (CoequalizerEqAr (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel (subst_univ_internal_eqrel s r)))))
              as q.
          rewrite !comp_in_cod_fib in q.
          cbn in q.
          refine (!_).
          rewrite !assoc.
          assert (TODO : ∏ A : UU, A).
          {
            admit.
          }
          simple refine (_ @ maponpaths (λ z, z · _) q @ _).
          * admit.
          * cbn.
            refine (_ · CoequalizerArrow _).
            refine (cod_mor _ · _).
          * rewrite !assoc'.
            refine (!_).
            etrans.
            {
              do 2 apply maponpaths.
              rewrite !assoc.
              apply maponpaths_2.
              apply mor_eq.
            }
            Check
       (quot_internal_type_eqrel HC PB
          (univ_internal_rel_to_type_eqrel (subst_univ_internal_eqrel s r)))).
            refine
          cbn
          apply q.

          pose (mor_eq
      (internal_relation_src
         (internal_type_eqrel_to_internal_slice_eqrel PB (cat_el_map_mor el a)
            (univ_internal_rel_to_type_eqrel r)))).
          pose (mor_eq
                  (CoequalizerArrow (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r)))).
          cbn in p0.
          cbn in p1.
          cbn in q.
          Check cat_el_map_pb_mor_comm el s a.
          unfold subst_univ_internal_rel_mor.
          admit.
        +

        cbn.
      Check CoequalizerOut (
      use mor_from_quot_internal_type_eqrel.
      - use PullbackArrow.
        + exact (cat_el_map_mor _ _).
        + refine  cbn.
          _ _ _ · ).
          refine (cat_el_map_mor el a · _).
          cbn.
        cbn.
      refine .
      Check (pr211 (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r))).

    cod_dom
      (quot_internal_type_eqrel HC PB
         (univ_internal_rel_to_type_eqrel (subst_univ_internal_eqrel s r))),
  cod_dom (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r))

    Check (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r)).
    use mor_from_quot_internal_type_eqrel.
    - refine (cat_el_map_pb_mor _ _ _ · _).
      exact (dom_mor
               (CoequalizerArrow
                  (quot_internal_type_eqrel HC PB (univ_internal_rel_to_type_eqrel r)))).
    - cbn.

  Admitted.

  Proposition isaprop_is_stable_cat_univ_trunc
              (ta : cat_univ_codes_trunc)
    : isaprop (is_stable_cat_univ_trunc ta).
  Proof.
    repeat (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_trunc
    : UU
    := ∑ (ta : cat_univ_codes_trunc),
       is_stable_cat_univ_trunc ta.

  Coercion cat_univ_stable_codes_trunc_to_codes
           (ta : cat_univ_stable_codes_trunc)
    : cat_univ_codes_trunc
    := pr1 ta.

  Proposition cat_univ_stable_codes_trunc_stable
              (ta : cat_univ_stable_codes_trunc)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
    : s · cat_univ_trunc_code ta a
      =
      cat_univ_trunc_code ta (s · a).
  Proof.
    exact (pr1 (pr2 ta Γ Δ s a)).
  Defined.

  Proposition cat_univ_stable_codes_trunc_z_iso_stable
              (ta : cat_univ_stable_codes_trunc)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
    : cat_el_map_pb_mor el _ _
      · cat_univ_trunc_z_iso ta a
      =
      cat_el_map_el_eq el (cat_univ_stable_codes_trunc_stable ta s a)
      · cat_univ_trunc_z_iso ta (s · a)
      · regular_category_im_map
          HC
          _
          _
          (cat_el_map_pb_mor el _ _)
          s
          (!(cat_el_map_pb_mor_comm el s a)).
  Proof.
    exact (pr2 (pr2 ta Γ Δ s a)).
  Defined.

  Proposition cat_univ_stable_codes_trunc_eq
              {ta₁ ta₂ : cat_univ_stable_codes_trunc}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C),
                   cat_univ_trunc_code ta₁ a
                   =
                   cat_univ_trunc_code ta₂ a)
              (q : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C),
                  cat_el_map_el_eq el (!(p Γ a)) · cat_univ_trunc_z_iso ta₁ a
                  =
                  cat_univ_trunc_z_iso ta₂ a)
    : ta₁ = ta₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_trunc.
    }
    use cat_univ_codes_trunc_eq.
    - exact p.
    - exact q.
  Qed.

  Proposition isaset_cat_univ_stable_codes_trunc
    : isaset cat_univ_stable_codes_trunc.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_trunc.
    - intro.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_trunc.
  Qed.
End TruncInCatWithUniv.

Arguments cat_univ_codes_trunc {C} HC el.
Arguments cat_univ_stable_codes_trunc {C} HC el.

Section PreservationTruncCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_ob}
          {el₁ : cat_stable_el_map_coherent C₁}
          {el₂ : cat_stable_el_map_coherent C₂}
          (HC₁ : is_regular_category C₁)
          (HC₂ : is_regular_category C₂)
          {F : functor_finlim_ob C₁ C₂}
          (Fel : functor_preserves_el el₁ el₂ F)
          (ta₁ : cat_univ_stable_codes_trunc HC₁ el₁)
          (ta₂ : cat_univ_stable_codes_trunc HC₂ el₂).

  (** * 3. Preservation *)
  Definition functor_preserves_stable_trunc_code
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁),
       #F(cat_univ_trunc_code ta₁ a) · functor_on_universe F
       =
       cat_univ_trunc_code ta₂ (#F a · functor_on_universe F).

  Proposition functor_preserves_stable_codes_trunc_z_iso_path
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
    : cat_el_map_mor el₂ (#F a · functor_on_universe F) · identity _
      =
      inv_from_z_iso (functor_el_map_iso Fel a) · # F (cat_el_map_mor el₁ a).
  Proof.
    rewrite id_right.
    refine (!_).
    use z_iso_inv_on_right.
    apply functor_el_map_comm.
  Qed.

  Definition functor_preserves_stable_codes_trunc_z_iso
             (p : functor_preserves_stable_trunc_code)
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁),
       #F(cat_univ_trunc_z_iso ta₁ a)
       =
       functor_el_map_iso Fel _
       · cat_el_map_el_eq el₂ (p Γ a)
       · cat_univ_trunc_z_iso ta₂ _
       · regular_category_im_map
           HC₂
           _
           _
           (inv_from_z_iso (functor_el_map_iso Fel a))
           (identity _)
           (functor_preserves_stable_codes_trunc_z_iso_path a)
       · regular_functor_preserves_im_inv HC₁ HC₂ (functor_finlim_preserves_pullback F) _.

  Definition functor_preserves_stable_trunc
    : UU
    := ∑ (p : functor_preserves_stable_trunc_code),
       functor_preserves_stable_codes_trunc_z_iso p.

  Proposition isaprop_functor_preserves_stable_trunc
    : isaprop functor_preserves_stable_trunc.
  Proof.
    use isaproptotal2.
    - intro.
      repeat (use impred ; intro).
      apply homset_property.
    - intros.
      repeat (use funextsec ; intro).
      apply homset_property.
  Qed.

  Definition make_functor_preserves_stable_trunc
             (p : functor_preserves_stable_trunc_code)
             (q : functor_preserves_stable_codes_trunc_z_iso p)
    : functor_preserves_stable_trunc
    := p ,, q.

  Proposition functor_preserves_stable_trunc_on_code
              (p : functor_preserves_stable_trunc)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
    : #F(cat_univ_trunc_code ta₁ a) · functor_on_universe F
      =
      cat_univ_trunc_code ta₂ (#F a · functor_on_universe F).
  Proof.
    exact (pr1 p Γ a).
  Defined.

  Proposition functor_preserves_stable_trunc_on_z_iso
              (p : functor_preserves_stable_trunc)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
    : #F(cat_univ_trunc_z_iso ta₁ a)
      =
      functor_el_map_iso Fel _
      · cat_el_map_el_eq el₂ (functor_preserves_stable_trunc_on_code p a)
      · cat_univ_trunc_z_iso ta₂ _
      · regular_category_im_map
          HC₂
          _
          _
          (inv_from_z_iso (functor_el_map_iso Fel a))
          (identity _)
          (functor_preserves_stable_codes_trunc_z_iso_path a)
      · regular_functor_preserves_im_inv HC₁ HC₂ (functor_finlim_preserves_pullback F) _.
  Proof.
    exact (pr2 p Γ a).
  Defined.
End PreservationTruncCodes.

Arguments functor_preserves_stable_trunc_code
            {C₁ C₂ el₁ el₂ HC₁ HC₂} F ta₁ ta₂.
Arguments functor_preserves_stable_codes_trunc_z_iso
  {C₁ C₂ el₁ el₂ HC₁ HC₂ F} Fel {ta₁ ta₂}.
Arguments functor_preserves_stable_trunc_on_code
  {C₁ C₂ el₁ el₂ HC₁ HC₂ F Fel ta₁ ta₂} p {Γ} a.
Arguments functor_preserves_stable_trunc_on_z_iso
  {C₁ C₂ el₁ el₂ HC₁ HC₂ F Fel ta₁ ta₂} p {Γ} a.

(** * 4. Preservation by identity and composition *)
Proposition id_preserves_stable_trunc_code
            {C : univ_cat_with_finlim_ob}
            (HC : is_regular_category C)
            {el : cat_stable_el_map_coherent C}
            (ta : cat_univ_stable_codes_trunc HC el)
  : functor_preserves_stable_trunc_code (identity _) ta ta.
Proof.
  intros Γ a ; cbn.
  rewrite id_right.
  use cat_univ_trunc_code_eq.
  rewrite id_right.
  apply idpath.
Qed.

Proposition id_preserves_stable_codes_trunc_z_iso
            {C : univ_cat_with_finlim_ob}
            (HC : is_regular_category C)
            {el : cat_stable_el_map_coherent C}
            (ta : cat_univ_stable_codes_trunc HC el)
  : functor_preserves_stable_codes_trunc_z_iso
      (id_functor_preserves_el el)
      (id_preserves_stable_trunc_code HC ta).
Proof.
  intros Γ a ; cbn.
  etrans.
  {
    refine (!_).
    exact (cat_univ_trunc_z_iso_eq _ (!(id_right _))).
  }
  rewrite cat_el_map_el_eq_comp.
  rewrite !assoc'.
  use maponpaths_compose.
  {
    apply cat_el_map_el_eq_eq.
  }
  apply maponpaths.
  use (regular_category_mor_to_im_eq HC).
  - exact (cat_el_map_el_eq el (id_right _)).
  - apply identity.
  - refine (id_right _ @ _).
    rewrite cat_el_map_mor_eq.
    apply idpath.
  - rewrite regular_category_im_map_left.
    apply idpath.
  - rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      apply (regular_functor_preserves_im_inv_left HC HC (identity_preserves_pullback _)).
    }
    apply regular_category_im_map_left.
  - etrans.
    {
      apply regular_category_im_map_right.
    }
    apply maponpaths_2.
    apply cat_el_map_el_eq_eq.
  - rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply regular_category_im_map_right.
    }
    rewrite !assoc'.
    apply maponpaths.
    apply (regular_functor_preserves_im_inv_right HC HC (identity_preserves_pullback _)).
Qed.

Proposition id_preserves_stable_trunc
            {C : univ_cat_with_finlim_ob}
            (HC : is_regular_category C)
            {el : cat_stable_el_map_coherent C}
            (ta : cat_univ_stable_codes_trunc HC el)
  : functor_preserves_stable_trunc
      HC HC
      (id_functor_preserves_el el)
      ta
      ta.
Proof.
  use make_functor_preserves_stable_trunc.
  - exact (id_preserves_stable_trunc_code HC ta).
  - exact (id_preserves_stable_codes_trunc_z_iso HC ta).
Qed.

Section CompPreservation.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim_ob}
          {el₁ : cat_stable_el_map_coherent C₁}
          {el₂ : cat_stable_el_map_coherent C₂}
          {el₃ : cat_stable_el_map_coherent C₃}
          {HC₁ : is_regular_category C₁}
          {HC₂ : is_regular_category C₂}
          {HC₃ : is_regular_category C₃}
          {ta₁ : cat_univ_stable_codes_trunc HC₁ el₁}
          {ta₂ : cat_univ_stable_codes_trunc HC₂ el₂}
          {ta₃ : cat_univ_stable_codes_trunc HC₃ el₃}
          {F : functor_finlim_ob C₁ C₂}
          {Fel : functor_preserves_el el₁ el₂ F}
          (Fc : functor_preserves_stable_trunc HC₁ HC₂ Fel ta₁ ta₂)
          {G : functor_finlim_ob C₂ C₃}
          {Gel : functor_preserves_el el₂ el₃ G}
          (Gc : functor_preserves_stable_trunc HC₂ HC₃ Gel ta₂ ta₃).

  Proposition comp_preserves_stable_trunc_code
    : functor_preserves_stable_trunc_code (F · G) ta₁ ta₃.
  Proof.
    intros Γ a ; cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      apply (functor_preserves_stable_trunc_on_code Fc).
    }
    etrans.
    {
      apply (functor_preserves_stable_trunc_on_code Gc).
    }
    use cat_univ_trunc_code_eq.
    rewrite !functor_comp.
    rewrite !assoc'.
    apply idpath.
  Qed.

  Proposition comp_preserves_stable_codes_trunc_z_iso
    : functor_preserves_stable_codes_trunc_z_iso
        (comp_functor_preserves_el Fel Gel)
        comp_preserves_stable_trunc_code.
  Proof.
    intros Γ a ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_preserves_stable_trunc_on_z_iso Fc).
    }
    etrans.
    {
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      apply functor_comp.
    }
    do 3 refine (assoc' _ _ _ @ _).
    do 4 refine (_ @ assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (functor_preserves_stable_trunc_on_z_iso Gc).
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply functor_el_map_iso_eq_alt.
    }
    do 5 refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 5 apply maponpaths_2.
      apply cat_el_map_el_eq_comp.
    }
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths_2.
      apply cat_el_map_el_eq_comp.
    }
    do 2 refine (assoc' _ _ _ @ _).
    refine (!_).
    use z_iso_inv_to_left.
    etrans.
    {
      rewrite cat_el_map_el_eq_inv.
      do 5 (refine (assoc _ _ _ @ _) ; apply maponpaths_2).
      apply cat_el_map_el_eq_comp.
    }
    assert (#G(#F a · functor_on_universe F) · functor_on_universe G
            =
            #G(#F a) · (#G (functor_on_universe F) · functor_on_universe G))
      as p.
    {
      rewrite functor_comp.
      rewrite assoc.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(cat_univ_trunc_z_iso_eq ta₃ (!p))).
    }
    do 2 refine (assoc' _ _ _ @ _).
    do 4 refine (_ @ assoc _ _ _).
    use maponpaths_compose.
    {
      apply cat_el_map_el_eq_eq.
    }
    apply maponpaths.
    use (MonicisMonic
           _
           (functor_preserves_pb_on_monic
              (functor_finlim_preserves_pullback G)
              (functor_preserves_pb_on_monic
                 (functor_finlim_preserves_pullback F)
                 (regular_category_im_Monic HC₁ _)))).
    refine (!_).
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      do 2 (apply maponpaths ; refine (assoc' _ _ _ @ _)).
      apply maponpaths.
      refine (!(functor_comp G _ _) @ _).
      apply maponpaths.
      apply regular_functor_preserves_im_inv_left.
    }
    etrans.
    {
      do 2 apply maponpaths.
      refine (!(functor_comp G _ _) @ _).
      apply maponpaths.
      apply regular_category_im_map_left.
    }
    rewrite id_right.
    etrans.
    {
      apply maponpaths.
      apply regular_functor_preserves_im_inv_left.
    }
    etrans.
    {
      apply regular_category_im_map_left.
    }
    rewrite id_right.
    refine (!_).
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply (regular_functor_preserves_im_inv_left
               HC₁ HC₃
               (composition_preserves_pullback
                  (functor_finlim_preserves_pullback F)
                  (functor_finlim_preserves_pullback G))).
    }
    etrans.
    {
      apply maponpaths.
      apply regular_category_im_map_left.
    }
    rewrite id_right.
    etrans.
    {
      apply regular_category_im_map_left.
    }
    apply id_right.
  Qed.

  Proposition comp_preserves_stable_trunc
    : functor_preserves_stable_trunc
        HC₁ HC₃
        (comp_functor_preserves_el Fel Gel)
        ta₁ ta₃.
  Proof.
    use make_functor_preserves_stable_trunc.
    - exact comp_preserves_stable_trunc_code.
    - exact comp_preserves_stable_codes_trunc_z_iso.
  Qed.
End CompPreservation.

(** * 5. Univalence condition *)
Proposition cat_univ_stable_trunc_univalence_lemma
            {C : univ_cat_with_finlim_ob}
            {HC : is_regular_category C}
            {el : cat_stable_el_map_coherent C}
            {ta₁ ta₂ : cat_univ_stable_codes_trunc HC el}
            (Fc : functor_preserves_stable_trunc
                    HC HC
                    (id_functor_preserves_el el)
                    ta₁
                    ta₂)
  : ta₁ = ta₂.
Proof.
  use cat_univ_stable_codes_trunc_eq.
  - intros Γ a.
    pose (functor_preserves_stable_trunc_on_code Fc a) as p.
    cbn in p.
    rewrite id_right in p.
    refine (p @ _).
    use cat_univ_trunc_code_eq.
    apply id_right.
  - intros Γ a.
    etrans.
    {
      apply maponpaths.
      exact (functor_preserves_stable_trunc_on_z_iso Fc a).
    }
    simpl.
    rewrite !assoc.
    rewrite !cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      refine (!_).
      apply (cat_univ_trunc_z_iso_eq ta₂ (!(id_right _))).
    }
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    refine (_ @ assoc _ _ _).
    use maponpaths_compose.
    {
      apply cat_el_map_el_eq_eq.
    }
    apply maponpaths.
    use (MonicisMonic _ (regular_category_im_Monic _ _)).
    rewrite regular_category_im_map_left.
    rewrite assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (regular_functor_preserves_im_inv_left
               HC HC
               (identity_preserves_pullback _)).
    }
    apply regular_category_im_map_left.
Qed.
