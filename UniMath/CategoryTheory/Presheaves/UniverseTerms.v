(**

 Terms of the universe of presheaves

 We showed that every universe of sets gives rise to a universe of presheaves
 via the Hofmann-Streicher lifting. In this file, we look at terms of the
 universe. We show that terms of the universe in the empty context are the
 same as small presheaves (i.e., presheaf valued in the given universe of sets),
 and we characterize terms of the universe in some context given by a small
 presheaf. This characterization uses small dependent presheaves, which are
 almost the same as dependent presheaves but with one difference: rather than
 `hSet`, they are valued in the given universe of sets.

 The reason why we characterise terms of the universe, is as follows. The
 universe of presheaves allows us to strictify the presheaf model of type
 theory. By only looking at presheaves valued in some set universe of sets,
 we obtain a CwF. Contexts are terms of the universe in the empty context,
 and types are small dependent presheaves. Hence, the characterisations in
 this file can be used to give simpler descriptions of contexts and types in
 the strictified presheaf model.

 Content
 1. Terms of the universe in the empty context
 1.1. Terms give rise to functors
 1.2. Functors give rise to terms
 1.3. Inverse laws
 1.4. The equivalence
 2. Terms of the universe in a given context
 2.1. To dependent presheaves
 2.2. To terms
 2.3. Inverse laws
 2.4. The equivalence

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.SetUniverses.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.UniverseToCat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.UniverseLifting.

Local Open Scope cat.

Section TermsUniverse.
  Context {C : category}
          {u : set_universe}.

  (** * 1. Terms of the universe in the empty context *)

  (** * 1.1. Terms give rise to functors *)
  Section TermToFunctor.
    Context (τ : psh_term
                   (presheaf_universe_ctx
                      u
                      (constant_functor (C^op) HSET unitset))).

    Definition psh_term_universe_to_functor_data
      : functor_data C^op (set_universe_to_setcategory u).
    Proof.
      use make_functor_data.
      - exact (λ x, (τ x tt : _ ⟶ _) (cod_fib_id (C := C) x)).
      - exact (λ x y f a,
               set_universe_eq
                 (presheaf_el_map_path C _ _ _ (idpath _))
                 (#(τ x tt : _ ⟶ _) (cod_fib_comp_mor (C := C) f) a)).
    Defined.

    Proposition psh_term_universe_to_functor_laws
      : is_functor psh_term_universe_to_functor_data.
    Proof.
      split.
      - intros x.
        use funextsec.
        intro a.
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (psh_term_universe_id _ _ _ _ _).
        }
        rewrite set_universe_eq_comp.
        apply set_universe_eq_idpath.
      - intros x y z f g.
        use funextsec.
        intro a.
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (psh_term_universe_comp _ _ _ _ _ _ _).
        }
        rewrite set_universe_eq_comp.
        use set_universe_eq_path'.
        apply maponpaths.
        apply set_universe_eq_path.
    Qed.

    Definition psh_term_universe_to_functor
      : C^op ⟶ set_universe_to_setcategory u.
    Proof.
      use make_functor.
      - exact psh_term_universe_to_functor_data.
      - exact psh_term_universe_to_functor_laws.
    Defined.
  End TermToFunctor.

  (** * 1.2. Functors give rise to terms *)
  Section FunctorToTerm.
    Context (τ : C^op ⟶ set_universe_to_setcategory u).

    Definition functor_to_psh_term_universe_data
      : psh_term_data
          (presheaf_universe_ctx
             u
             (constant_functor (C^op) HSET unitset))
      := λ x _, functor_op (slice_dom x) ∙ τ.

    Arguments functor_to_psh_term_universe_data /.

    Proposition functor_to_psh_term_universe_law
      : psh_term_law functor_to_psh_term_universe_data.
    Proof.
      intros x y f xx.
      use functor_eq.
      {
        apply homset_property.
      }
      apply idpath.
    Qed.

    Definition functor_to_psh_term_universe
      : psh_term
          (presheaf_universe_ctx
             u
             (constant_functor (C^op) HSET unitset)).
    Proof.
      use make_psh_term.
      - exact functor_to_psh_term_universe_data.
      - exact functor_to_psh_term_universe_law.
    Defined.
  End FunctorToTerm.

  (** * 1.3. Inverse laws *)
  Proposition functor_to_psh_term_universe_to_functor
              (τ : C^op ⟶ set_universe_to_setcategory u)
    : psh_term_universe_to_functor (functor_to_psh_term_universe τ)
      =
      τ.
  Proof.
    use functor_eq.
    {
      apply homset_property.
    }
    refine (maponpaths (λ z, _ ,, z) _).
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro f.
    use funextsec ; intro a.
    cbn.
    apply set_universe_eq_idpath.
  Qed.

  Local Lemma psh_term_to_functor_to_psh_term_universe_lem_1
              {x : C}
              (g : C/x)
    : cod_fib_comp (cod_mor g) (cod_fib_id (cod_dom g)) = g.
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    cbn.
    apply id_left.
  Defined.

  Local Lemma psh_term_to_functor_to_psh_term_universe_lem_2
              {x : C}
              {g₁ g₂ : C/x}
              (h : g₂ --> g₁)
    : cod_fib_comp (cod_mor g₁) (cod_fib_comp (dom_mor h) (cod_fib_id (cod_dom g₂)))
      =
      g₂.
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    cbn.
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    exact (mor_eq h).
  Defined.

  Proposition psh_term_to_functor_to_psh_term_universe
              (τ : psh_term
                     (presheaf_universe_ctx
                        u
                        (constant_functor (C^op) HSET unitset)))
    : functor_to_psh_term_universe (psh_term_universe_to_functor τ)
      =
      τ.
  Proof.
    use psh_term_eq.
    intros x xx.
    induction xx.
    use path_functor_to_set_universe.
    - cbn.
      intro h.
      pose (functor_to_set_universe_eq_ob
              (psh_term_naturality τ (cod_mor h) tt)
              (cod_fib_id (cod_dom h)))
        as p.
      cbn in p.
      refine (p @ _).
      apply maponpaths.
      refine (maponpaths (λ z, _ ,, z) _).
      cbn.
      apply id_left.
    - intros g₁ g₂ h a.
      refine (set_universe_eq_comp _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (functor_to_set_universe_eq (psh_term_naturality τ (cod_mor g₁) tt)).
      }
      cbn.
      refine (set_universe_eq_comp _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        refine (set_universe_eq_comp _ _ _ @ _).
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        use (functor_to_set_universe_mor_eq
               _
               (g := h)
               (psh_term_to_functor_to_psh_term_universe_lem_1 g₁)
               (psh_term_to_functor_to_psh_term_universe_lem_2 h)).
        use eq_mor_cod_fib.
        refine (comp_in_cod_fib _ _ @ _).
        refine (_ @ !(comp_in_cod_fib _ _)).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply (idtoiso_opp (psh_term_to_functor_to_psh_term_universe_lem_2 h)).
          }
          exact (dom_mor_idtoiso _).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply (idtoiso_opp (psh_term_to_functor_to_psh_term_universe_lem_1 _)).
          }
          exact (dom_mor_idtoiso _).
        }
        cbn.
        rewrite !maponpathsinv0.
        etrans.
        {
          do 4 apply maponpaths.
          unfold psh_term_to_functor_to_psh_term_universe_lem_1.
          refine (maponpathscomp (λ z, _ ,, z) cod_dom _ @ _).
          unfold funcomp ; cbn.
          apply maponpaths_for_constant_function.
        }
        cbn.
        rewrite id_right.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          do 3 apply maponpaths.
          unfold psh_term_to_functor_to_psh_term_universe_lem_2.
          refine (maponpathscomp (λ z, _ ,, z) cod_dom (assoc' _ _ _ @ _ @ _) @ _).
          unfold funcomp ; cbn.
          apply maponpaths_for_constant_function.
        }
        cbn.
        rewrite id_left.
        apply idpath.
      }
      refine (set_universe_eq_comp _ _ _ @ _).
      rewrite set_universe_eq_idpath.
      apply maponpaths.
      rewrite set_universe_eq_comp.
      apply set_universe_eq_idpath.
  Qed.

  (** * 1.4. The equivalence *)
  Definition functor_weq_psh_term_universe
    : psh_term
        (presheaf_universe_ctx
           u
           (constant_functor (C^op) HSET unitset))
      ≃
      C^op ⟶ set_universe_to_setcategory u.
  Proof.
    use weq_iso.
    - exact psh_term_universe_to_functor.
    - exact functor_to_psh_term_universe.
    - exact psh_term_to_functor_to_psh_term_universe.
    - exact functor_to_psh_term_universe_to_functor.
  Defined.

  (** * 2. Terms of the universe in a given context *)
  Section SetUniversePshType.
    Context {τ : psh_term
                   (presheaf_universe_ctx
                      u
                      (constant_functor (C^op) HSET unitset))}.

    (** * 2.1. To dependent presheaves *)
    Section ToDepPsh.
      Context (θ : psh_term
                     (presheaf_universe_ctx
                        u
                        (total_psh (presheaf_el_map τ)))).

      Definition psh_term_to_set_universe_dep_psh_data
        : set_universe_dep_psh_data (psh_term_universe_to_functor τ).
      Proof.
        use make_set_universe_dep_psh_data.
        - intros x a.
          exact ((θ x (tt ,, a) : _ ⟶ _) (cod_fib_id x)).
        - cbn.
          intros x y xx yy s p a.
          refine (set_universe_eq
                    _
                    (#(θ x (tt ,, xx) : _ ⟶ _) (cod_fib_comp_mor s) a)).
          abstract
            (pose (functor_to_set_universe_eq_ob
                     (psh_term_naturality θ s (tt ,, xx))
                     (cod_fib_id y))
              as q ;
             cbn in q ;
             refine (!q @ _) ;
             apply maponpaths_2 ;
             do 3 apply maponpaths ;
             induction p ;
             apply set_universe_eq_path).
      Defined.

      Proposition psh_term_to_set_universe_dep_psh_laws
        : set_universe_dep_psh_laws
            psh_term_to_set_universe_dep_psh_data.
      Proof.
        split.
        - cbn.
          intros x xx p a.
          etrans.
          {
            apply maponpaths.
            apply psh_term_universe_id.
          }
          rewrite set_universe_eq_comp.
          apply set_universe_eq_idpath.
        - intros x y z xx yy zz s₁ s₂ p q r a.
          induction p, q.
          cbn.
          etrans.
          {
            apply maponpaths.
            apply psh_term_universe_comp.
          }
          refine (set_universe_eq_comp _ _ _ @ _).
          use set_universe_eq_path'.
          apply maponpaths.
          apply set_universe_eq_path.
      Qed.

      Definition psh_term_to_set_universe_dep_psh
        : set_universe_dep_psh (psh_term_universe_to_functor τ).
      Proof.
        use make_set_universe_dep_psh.
        - exact psh_term_to_set_universe_dep_psh_data.
        - exact psh_term_to_set_universe_dep_psh_laws.
      Defined.
    End ToDepPsh.

    (** * 2.2. To terms *)
    Section ToTerm.
      Context (θ : set_universe_dep_psh (psh_term_universe_to_functor τ)).

      Local Lemma set_universe_dep_psh_to_psh_term_data_mor_eq_lem
                  {x : C}
                  {g₁ g₂ : (C/x)^op}
                  (h : g₁ --> g₂)
        : cod_fib_comp
            (cod_mor g₁)
            (cod_fib_comp (dom_mor h) (cod_fib_id (cod_dom g₂)))
          =
          cod_fib_comp (cod_mor g₂) (cod_fib_id (cod_dom g₂)).
      Proof.
        refine (maponpaths (λ z, _ ,, z) _).
        abstract
          (cbn ;
           rewrite !id_left ;
           exact (mor_eq h)).
      Defined.

      Local Lemma set_universe_dep_psh_to_psh_term_data_mor_eq
                  {x : C}
                  (xx : presheaf_el_map τ x tt)
                  {g₁ g₂ : (C/x)^op}
                  (h : g₁ --> g₂)
        : set_universe_eq
            (presheaf_el_map_path C u τ (dom_mor h) (idpath tt))
            (# (τ (cod_dom g₁) tt : _ ⟶ _)
               (cod_fib_comp_mor (dom_mor h))
               (set_universe_eq
                  (presheaf_el_map_path C u _ _ (idpath _))
                  (# (τ x tt : _ ⟶ _) (cod_fib_comp_mor (cod_mor g₁)) xx)))
          =
          set_universe_eq
            (presheaf_el_map_path C u _ _ (idpath _))
            (# (τ x tt : _ ⟶ _) (cod_fib_comp_mor (cod_mor g₂)) xx).
      Proof.
        cbn.
        etrans.
        {
          apply maponpaths.
          use (functor_to_set_universe_eq
                 (psh_term_naturality τ (cod_mor g₁) tt)).
        }
        cbn.
        rewrite !set_universe_eq_comp.
        rewrite set_universe_eq_idpath.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            exact (!(eqtohomot (functor_comp (τ x tt) _ _) xx)).
          }
          use (functor_to_set_universe_mor_eq _ (idpath _) _).
          - exact (cod_fib_comp (cod_mor g₂) (cod_fib_id (cod_dom g₂))).
          - exact (cod_fib_comp_mor (cod_mor g₂)).
          - apply set_universe_dep_psh_to_psh_term_data_mor_eq_lem.
          - refine (_ @ !(id_left _)).
            use eq_mor_cod_fib.
            refine (comp_in_cod_fib _ _ @ _).
            etrans.
            {
              apply maponpaths.
              apply comp_in_cod_fib.
            }
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                apply (idtoiso_opp (C := C/x)).
              }
              refine (dom_mor_idtoiso _ @ _).
              unfold set_universe_dep_psh_to_psh_term_data_mor_eq_lem.
              rewrite maponpathsinv0.
              do 3 apply maponpaths.
              refine (maponpathscomp (λ z, _ ,, z) cod_dom _ @ _).
              unfold funcomp ; cbn.
              apply maponpaths_for_constant_function.
            }
            cbn.
            rewrite id_left.
            exact (mor_eq h).
        }
        rewrite set_universe_eq_comp.
        use set_universe_eq_path'.
        apply maponpaths.
        apply set_universe_eq_idpath.
      Qed.

      Definition set_universe_dep_psh_to_psh_term_data_functor_data
                 (x : C)
                 (xx : (total_psh (presheaf_el_map τ) x : hSet))
        : functor_data (C/x)^op (set_universe_to_category u).
      Proof.
        induction xx as [ [] xx ].
        use make_functor_data.
        - intro y.
          refine (θ (cod_dom y)
                    (set_universe_eq
                       _
                       (#(τ x _ : _ ⟶ _) (cod_fib_comp_mor (cod_mor y)) xx))).
          apply presheaf_el_map_path.
          apply idpath.
        - cbn.
          intros g₁ g₂ h a.
          refine (#s θ (pr1 h) _ a).
          exact (set_universe_dep_psh_to_psh_term_data_mor_eq xx h).
      Defined.

      Proposition set_universe_dep_psh_to_psh_term_data_functor_laws
                  (x : C)
                  (xx : (total_psh (presheaf_el_map τ) x : hSet))
        : is_functor (set_universe_dep_psh_to_psh_term_data_functor_data x xx).
      Proof.
        induction xx as [ [] xx ].
        split.
        - intros g.
          use funextsec.
          intro a.
          cbn.
          apply set_universe_dep_psh_id.
        - intros g₁ g₂ g₃ h₁ h₂.
          use funextsec.
          intro a.
          cbn -[fiber_category].
          etrans.
          {
            apply (set_universe_dep_psh_mor_eq _ _ (comp_in_cod_fib _ _)).
          }
          apply (set_universe_dep_psh_comp θ).
      Qed.

      Definition set_universe_dep_psh_to_psh_term_data
        : psh_term_data
            (presheaf_universe_ctx
               u
               (total_psh (presheaf_el_map τ))).
      Proof.
        intros x xx.
        use make_functor.
        - exact (set_universe_dep_psh_to_psh_term_data_functor_data x xx).
        - exact (set_universe_dep_psh_to_psh_term_data_functor_laws x xx).
      Defined.

      Arguments set_universe_dep_psh_to_psh_term_data /.

      Proposition set_universe_dep_psh_to_psh_term_law
        : psh_term_law set_universe_dep_psh_to_psh_term_data.
      Proof.
        intros x y f xx.
        induction xx as [ [] xx ].
        use path_functor_to_set_universe.
        - abstract
            (intro g ;
             cbn ;
             apply maponpaths ;
             refine (!_) ;
             etrans ;
             [ apply maponpaths ;
               apply psh_term_universe_comp
             | ] ;
             rewrite set_universe_eq_comp ;
             use set_universe_eq_path' ;
             apply maponpaths ;
             apply set_universe_eq_path).
        - intros g₁ g₂ h a.
          cbn -[comp_functor].
          etrans.
          {
            apply maponpaths.
            use set_universe_dep_psh_mor_eq.
            - exact (dom_mor (# (comp_functor f) h)).
            - apply idpath.
          }
          cbn.
          simple refine (maponpaths _ (set_universe_dep_psh_eq _ _ _ _ _ _ _)
                         @ set_universe_eq_comp _ _ _
                         @ set_universe_eq_idpath _ _
                         @ _).
          + etrans.
            {
              apply maponpaths.
              apply (psh_term_universe_comp _ _ τ).
            }
            rewrite set_universe_eq_comp.
            use set_universe_eq_path'.
            apply maponpaths.
            apply set_universe_eq_path.
          + etrans.
            {
              apply maponpaths.
              apply (psh_term_universe_comp _ _ τ).
            }
            rewrite set_universe_eq_comp.
            use set_universe_eq_path'.
            apply maponpaths.
            apply set_universe_eq_path.
          + apply maponpaths_2.
            apply setproperty.
      Qed.

      Definition set_universe_dep_psh_to_psh_term
        : psh_term
            (presheaf_universe_ctx
               u
               (total_psh (presheaf_el_map τ))).
      Proof.
        use make_psh_term.
        - exact set_universe_dep_psh_to_psh_term_data.
        - exact set_universe_dep_psh_to_psh_term_law.
      Defined.
    End ToTerm.

    Arguments set_universe_dep_psh_to_psh_term_data /.

    (** * 2.3. Inverse laws *)
    Proposition psh_term_to_set_universe_dep_psh_to_psh_term
                (θ : psh_term
                       (presheaf_universe_ctx u (total_psh (presheaf_el_map τ))))
      : set_universe_dep_psh_to_psh_term
          (psh_term_to_set_universe_dep_psh θ)
        =
        θ.
    Proof.
      use psh_term_eq.
      intros x xx.
      induction xx as [ [] xx ].
      use path_functor_to_set_universe.
      - cbn -[op_category fiber_category] ; intros f.
        pose (functor_to_set_universe_eq_ob
                (psh_term_naturality θ (pr2 f) (tt ,, xx))
                (cod_fib_id (pr1 f)))
          as p.
        cbn in p.
        refine (_ @ p @ _).
        {
          apply maponpaths_2.
          do 3 apply maponpaths.
          apply set_universe_eq_path.
        }
        apply maponpaths.
        refine (maponpaths (λ z, _ ,, z) _).
        cbn.
        apply id_left.
      - intros g₁ g₂ h a.
        cbn.
        refine (set_universe_eq_comp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          pose (psh_term_naturality θ (cod_mor g₁) (tt ,, xx)).
          apply (functor_to_set_universe_eq (C := (C/_)^op) p).
        }
        cbn.
        refine (set_universe_eq_comp _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths.
          refine (set_universe_eq_comp _ _ _ @ _).
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          use (functor_to_set_universe_mor_eq
                 _
                 (g := h)
                 (psh_term_to_functor_to_psh_term_universe_lem_1 g₁)
                 (psh_term_to_functor_to_psh_term_universe_lem_2 h)).
          use eq_mor_cod_fib.
          refine (comp_in_cod_fib _ _ @ _).
          refine (_ @ !(comp_in_cod_fib _ _)).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              apply (idtoiso_opp (psh_term_to_functor_to_psh_term_universe_lem_2 h)).
            }
            exact (dom_mor_idtoiso _).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply (idtoiso_opp (psh_term_to_functor_to_psh_term_universe_lem_1 _)).
            }
            exact (dom_mor_idtoiso _).
          }
          cbn.
          rewrite !maponpathsinv0.
          etrans.
          {
            do 4 apply maponpaths.
            unfold psh_term_to_functor_to_psh_term_universe_lem_1.
            refine (maponpathscomp (λ z, _ ,, z) cod_dom _ @ _).
            unfold funcomp ; cbn.
            apply maponpaths_for_constant_function.
          }
          cbn.
          rewrite id_right.
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            do 3 apply maponpaths.
            unfold psh_term_to_functor_to_psh_term_universe_lem_2.
            refine (maponpathscomp (λ z, _ ,, z) cod_dom (assoc' _ _ _ @ _ @ _) @ _).
            unfold funcomp ; cbn.
            apply maponpaths_for_constant_function.
          }
          cbn.
          rewrite id_left.
          apply idpath.
        }
        refine (set_universe_eq_comp _ _ _ @ _).
        rewrite set_universe_eq_idpath.
        apply maponpaths.
        rewrite set_universe_eq_comp.
        apply set_universe_eq_idpath.
    Qed.

    Proposition set_universe_dep_psh_to_psh_term_to_dep_psh
                (θ : set_universe_dep_psh
                       (psh_term_universe_to_functor τ))
      : psh_term_to_set_universe_dep_psh
          (set_universe_dep_psh_to_psh_term θ)
        =
        θ.
    Proof.
      use set_universe_dep_psh_path.
      use set_universe_dep_psh_data_path.
      - intros x xx ; cbn.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply psh_term_universe_id.
        }
        rewrite set_universe_eq_comp.
        apply set_universe_eq_idpath.
      - cbn -[set_universe_dep_psh_to_psh_term_data].
        intros x y xx yy f p a.
        rewrite set_universe_eq_comp.
        cbn.
        refine (!_).
        simple refine (set_universe_dep_psh_eq _ _ _ _ _ _ _ @ set_universe_eq_path' _ _ _).
        + refine (_ @ p).
          etrans.
          {
            apply maponpaths.
            use (functor_to_set_universe_mor_eq _ (idpath _)).
            * exact (cod_fib_comp f (cod_fib_id y)).
            * exact (cod_fib_comp_mor f).
            * refine (maponpaths (λ z, _ ,, z) _).
              apply id_left.
            * refine (_ @ !(id_left _)).
              use eq_mor_cod_fib.
              refine (comp_in_cod_fib _ _ @ _).
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  apply (idtoiso_opp (C := C/x)).
                }
                exact (dom_mor_idtoiso _).
              }
              cbn.
              etrans.
              {
                apply maponpaths.
                apply id_left.
              }
              etrans.
              {
                apply maponpaths_2.
                rewrite maponpathsinv0.
                do 3 apply maponpaths.
                refine (maponpathscomp (λ z, _ ,, z) cod_dom _ @ _).
                unfold funcomp ; cbn.
                apply maponpaths_for_constant_function.
              }
              cbn.
              apply id_left.
          }
          rewrite set_universe_eq_comp.
          rewrite set_universe_eq_idpath.
          apply set_universe_eq_path.
        + etrans.
          {
            apply maponpaths.
            apply psh_term_universe_id.
          }
          rewrite set_universe_eq_comp.
          apply set_universe_eq_idpath.
        + apply maponpaths_2.
          apply setproperty.
    Qed.

    (** * 2.4. The equivalence *)
    Definition set_universe_dep_psh_weq_psh_term
      : psh_term
          (presheaf_universe_ctx
             u
             (total_psh (presheaf_el_map τ)))
        ≃
        set_universe_dep_psh (psh_term_universe_to_functor τ).
    Proof.
      use weq_iso.
      - exact psh_term_to_set_universe_dep_psh.
      - exact set_universe_dep_psh_to_psh_term.
      - exact psh_term_to_set_universe_dep_psh_to_psh_term.
      - exact set_universe_dep_psh_to_psh_term_to_dep_psh.
    Defined.
  End SetUniversePshType.
End TermsUniverse.

Arguments functor_weq_psh_term_universe : clear implicits.
Arguments set_universe_dep_psh_weq_psh_term : clear implicits.
