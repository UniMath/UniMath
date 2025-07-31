(**

 Universes as morphisms

 Universes in categories are usually defined as morphisms. More specifically, a universe in a
 category `C` with finite limits is given by a map `π : U_* --> U`. This map defines a class
 of small maps in `C` using that `C` has pullbacks.

 In the file `UniverseInCat.v` we defined universes in another way. A universe in a category `C`
 with finite limits is given by an object `U` together with a map assigning to each morphism
 `t : Γ --> U` a morphism `⌜ t ⌝ : El t --> Γ` satisfying suitable stability and coherence
 conditions. This definition is closer to what one has in type theory, and can more directly
 be compared to how one would define universes in comprehension categories.

 We show that these two definitions of universes are equivalent. Every morphism `π : U_* --> U`
 gives rise to a map `El` by taking the pullback. In addition, if we have a universe given by an
 object and a map `El`, then we obtain the morphism `π : U_* --> U` by taking `El (identity U)`.

 Content
 1. Every universe gives rise to a morphism
 2. Every morphism gives rise to a universe
 3. The maps are inverses
 4. The equivalence between morphisms and universes

                                                                                               *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.

Local Open Scope cat.

Section UniverseAsMorphism.
  Context (C : univ_cat_with_finlim_ob).

  (** * 1. Every universe gives rise to a morphism *)
  Definition cat_stable_el_map_coherent_to_mor
             (el : cat_stable_el_map_coherent C)
    : ∑ (e : C), e --> univ_cat_universe C.
  Proof.
    simple refine (_ ,, _).
    - exact (cat_el_map_el el (identity _)).
    - exact (cat_el_map_mor el (identity _)).
  Defined.

  (** * 2. Every morphism gives rise to a universe *)
  Section MorphismsToUniverse.
    Context {e : C}
            (p : e --> univ_cat_universe C).

    Definition cat_el_map_from_mor
      : cat_el_map C.
    Proof.
      intros Γ t.
      pose (P := pullbacks_univ_cat_with_finlim C _ _ _ p t).
      exact (PullbackObject P ,, PullbackPr2 P).
    Defined.

    Definition morphism_to_pb_mor_univ
               {Γ Δ : C}
               (s : Γ --> Δ)
               (t : Δ --> univ_cat_universe C)
      : pullbacks_univ_cat_with_finlim C (univ_cat_universe C) e Γ p (s · t)
        -->
        pullbacks_univ_cat_with_finlim C (univ_cat_universe C) e Δ p t.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _).
      - exact (PullbackPr2 _ · s).
      - abstract
          (rewrite !assoc' ;
           rewrite <- PullbackSqrCommutes ;
           apply idpath).
    Defined.

    Proposition morphism_to_pb_mor_univ_comm
                {Γ Δ : C}
                (s : Γ --> Δ)
                (t : Δ --> univ_cat_universe C)
      : morphism_to_pb_mor_univ s t
        · PullbackPr2
            (pullbacks_univ_cat_with_finlim
               C
               (univ_cat_universe C)
               e Δ p t)
        =
        PullbackPr2
          (pullbacks_univ_cat_with_finlim
             C
             (univ_cat_universe C)
             e Γ p (s · t))
        · s.
    Proof.
      apply PullbackArrow_PullbackPr2.
    Qed.

    Section UMP.
      Context {Γ Δ : C}
              (s : Γ --> Δ)
              (t : Δ --> univ_cat_universe C)
              {A : C}
              (h : A
                   -->
                   pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Δ p t)
              (k : A --> Γ)
              (q : h
                   · PullbackPr2
                       (pullbacks_univ_cat_with_finlim
                          C
                          (univ_cat_universe C) e Δ p t)
                   =
                   k · s).

      Definition is_pb_morphism_to_pb_mor_univ_mor
        : A
          -->
          pullbacks_univ_cat_with_finlim C (univ_cat_universe C) e Γ p (s · t).
      Proof.
        use PullbackArrow.
        - exact (h · PullbackPr1 _).
        - exact k.
        - abstract
            (rewrite !assoc ;
             rewrite <- q ;
             rewrite !assoc' ;
             rewrite <- PullbackSqrCommutes ;
             apply idpath).
      Defined.

      Proposition is_pb_morphism_to_pb_mor_univ_pr1
        : is_pb_morphism_to_pb_mor_univ_mor · morphism_to_pb_mor_univ s t
          =
          h.
      Proof.
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Δ p t))).
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          apply PullbackArrow_PullbackPr1.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          rewrite !assoc.
          unfold is_pb_morphism_to_pb_mor_univ_mor.
          rewrite PullbackArrow_PullbackPr2.
          rewrite q.
          apply idpath.
      Qed.

      Proposition is_pb_morphism_to_pb_mor_univ_unique
        : isaprop
            (∑ hk,
             (hk · morphism_to_pb_mor_univ s t = h)
             ×
             (hk
              · PullbackPr2
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Γ p (s · t))
              =
              k)).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Γ p (s · t)))).
        - pose proof (maponpaths
                        (λ z, z · PullbackPr1 _)
                        (pr12 ζ₁ @ !(pr12 ζ₂)))
            as r.
          cbn in r.
          unfold morphism_to_pb_mor_univ in r.
          rewrite !assoc' in r.
          rewrite PullbackArrow_PullbackPr1 in r.
          exact r.
        - refine (pr22 ζ₁ @ _).
          refine (_ @ !(pr22 ζ₂)).
          apply idpath.
      Qed.
    End UMP.

    Definition is_pb_morphism_to_pb_mor_univ
               {Γ Δ : C}
               (s : Γ --> Δ)
               (t : Δ --> univ_cat_universe C)
      : isPullback (morphism_to_pb_mor_univ_comm s t).
    Proof.
      intros A h k q ; cbn in q.
      use iscontraprop1.
      - apply is_pb_morphism_to_pb_mor_univ_unique.
      - simple refine (_ ,, _ ,, _).
        + exact (is_pb_morphism_to_pb_mor_univ_mor s t h k q).
        + exact (is_pb_morphism_to_pb_mor_univ_pr1 s t h k q).
        + abstract
            (cbn ;
             apply PullbackArrow_PullbackPr2).
    Defined.

    Definition cat_el_map_stable_from_mor
      : cat_el_map_stable cat_el_map_from_mor.
    Proof.
      intros Γ Δ s t.
      simple refine (_ ,, _ ,, _).
      - exact (morphism_to_pb_mor_univ s t).
      - exact (morphism_to_pb_mor_univ_comm s t).
      - exact (is_pb_morphism_to_pb_mor_univ s t).
    Defined.

    Definition cat_stable_el_map_from_mor
      : cat_stable_el_map C.
    Proof.
      use make_cat_stable_el_map.
      - exact cat_el_map_from_mor.
      - exact cat_el_map_stable_from_mor.
    Defined.

    Definition cat_el_map_el_eq_mor_from_mor
               {Γ : C}
               {t₁ t₂ : Γ --> univ_cat_universe C}
               (r : t₁ = t₂)
      : cat_el_map_el cat_stable_el_map_from_mor t₁
        -->
        cat_el_map_el cat_stable_el_map_from_mor t₂.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _).
      - exact (PullbackPr2 _).
      - abstract
          (rewrite r ;
           apply PullbackSqrCommutes).
    Defined.

    Proposition cat_el_map_el_eq_from_mor
                {Γ : C}
                {t₁ t₂ : Γ --> univ_cat_universe C}
                (r : t₁ = t₂)
      : pr1 (cat_el_map_el_eq cat_stable_el_map_from_mor r)
        =
        cat_el_map_el_eq_mor_from_mor r.
    Proof.
      induction r ; cbn ; unfold cat_el_map_el_eq_mor_from_mor.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - rewrite id_left.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      - rewrite id_left.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
    Qed.

    Proposition is_coherent_cat_stable_el_map_from_mor
      : is_coherent_cat_stable_el_map cat_stable_el_map_from_mor.
    Proof.
      split.
      - intros Γ t.
        refine (_ @ !(cat_el_map_el_eq_from_mor _)).
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
          exact (!(PullbackArrow_PullbackPr1 _ _ _ _ _)).
        + refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
          refine (_ @ !(PullbackArrow_PullbackPr2 _ _ _ _ _)).
          apply id_right.
      - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply cat_el_map_el_eq_from_mor.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + do 2 refine (assoc' _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
          exact (!(PullbackArrow_PullbackPr1 _ _ _ _ _)).
        + do 2 refine (assoc' _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          etrans.
          {
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            apply PullbackArrow_PullbackPr2.
          }
          etrans.
          {
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            apply PullbackArrow_PullbackPr2.
          }
          refine (_ @ !(PullbackArrow_PullbackPr2 _ _ _ _ _)).
          apply assoc'.
    Qed.

    Definition cat_stable_el_map_coherent_from_mor
      : cat_stable_el_map_coherent C.
    Proof.
      use make_cat_stable_el_map_coherent.
      - exact cat_stable_el_map_from_mor.
      - exact is_coherent_cat_stable_el_map_from_mor.
    Defined.
  End MorphismsToUniverse.

  (** * 3. The maps are inverses *)
  Section UniverseToMorphismToUniverse.
    Context (el : cat_stable_el_map_coherent C).

    Section Isomorphism.
      Context {Γ : C}
              (t : Γ --> univ_cat_universe C).

      Let P : Pullback (cat_el_map_mor el (id₁ (univ_cat_universe C))) t
        := cat_stable_el_map_pb el t (identity _).

      Definition mor_to_cat_el_map_to_mor_z_iso_mor
        : cat_el_map_el
            (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
            t
          -->
          cat_el_map_el el (t · identity _).
      Proof.
        use (PullbackArrow P _ _ _ _) ; cbn.
        - exact (PullbackPr1 _).
        - exact (PullbackPr2 _).
        - apply PullbackSqrCommutes.
      Defined.

      Definition mor_to_cat_el_map_to_mor_z_iso_inv
        : cat_el_map_el el (t · identity _)
          -->
          cat_el_map_el
            (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
            t.
      Proof.
        use PullbackArrow.
        - exact (cat_el_map_pb_mor el t (identity _)).
        - exact (cat_el_map_mor el _).
        - apply (PullbackSqrCommutes P).
      Defined.

      Proposition mor_to_cat_el_map_to_mor_z_iso_eqs
        : is_inverse_in_precat
            mor_to_cat_el_map_to_mor_z_iso_mor
            mor_to_cat_el_map_to_mor_z_iso_inv.
      Proof.
        split.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply PullbackArrow_PullbackPr1.
            }
            refine (PullbackArrow_PullbackPr1 P _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply PullbackArrow_PullbackPr2.
            }
            refine (PullbackArrow_PullbackPr2 P _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply (PullbackArrow_PullbackPr1 P).
            }
            refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply (PullbackArrow_PullbackPr2 P).
            }
            refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
      Qed.

      Definition mor_to_cat_el_map_to_mor_z_iso
        : z_iso
            (cat_el_map_el
               (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
               t)
            (cat_el_map_el el (t · identity _)).
      Proof.
        use make_z_iso.
        - exact mor_to_cat_el_map_to_mor_z_iso_mor.
        - exact mor_to_cat_el_map_to_mor_z_iso_inv.
        - exact mor_to_cat_el_map_to_mor_z_iso_eqs.
      Defined.
    End Isomorphism.

    Arguments mor_to_cat_el_map_to_mor_z_iso_mor /.

    Lemma mor_to_cat_el_map_to_mor_eq1
          {Γ : C}
          (t : Γ --> univ_cat_universe C)
      : mor_to_cat_el_map_to_mor_z_iso_mor t
        · cat_el_map_el_eq el (id_right t)
        · cat_el_map_mor el t
        =
        PullbackPr2 _.
    Proof.
      cbn.
      rewrite !assoc'.
      rewrite cat_el_map_mor_eq.
      exact (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el t (identity _)) _ _ _ _).
    Qed.

    Lemma mor_to_cat_el_map_to_mor_eq2
          {Γ Δ : C}
          (s : Γ --> Δ)
          (t : Δ --> univ_cat_universe C)
      : morphism_to_pb_mor_univ (cat_el_map_mor el (identity _)) s t
        · mor_to_cat_el_map_to_mor_z_iso_mor t
        · cat_el_map_el_eq el (id_right t)
        =
        mor_to_cat_el_map_to_mor_z_iso_mor (s · t)
        · cat_el_map_el_eq el (id_right (s · t))
        · cat_el_map_pb_mor el s t.
    Proof.
      rewrite !assoc'.
      assert (cat_el_map_el_eq el (id_right (s · t))
              · cat_el_map_pb_mor el s t
              =
              cat_el_map_el_eq el (assoc' _ _ _)
              · cat_el_map_pb_mor el s (t · identity _)
              · cat_el_map_el_eq el (id_right t))
        as ->.
      {
        refine (_ @ assoc _ _ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          use cat_el_map_pb_mor_eq.
          refine (assoc _ _ _ @ id_right _).
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (cat_el_map_el_eq_comp _ _ _ @ _).
        do 2 apply maponpaths.
        apply homset_property.
      }
      pose (P := cat_stable_el_map_pb el (s · t) (identity _)).
      rewrite !assoc.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (cat_stable_el_map_pb el t _))).
      - refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el t _)).
        }
        unfold morphism_to_pb_mor_univ.
        rewrite PullbackArrow_PullbackPr1.
        cbn.
        refine (!_).
        etrans.
        {
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          refine (!_).
          apply cat_el_map_pb_mor_comp.
        }
        apply (PullbackArrow_PullbackPr1 P).
      - refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el t _)).
        }
        unfold morphism_to_pb_mor_univ.
        rewrite PullbackArrow_PullbackPr2.
        cbn.
        refine (!_).
        assert (PullbackPr2 (cat_stable_el_map_pb el (s · t) (identity _)) · s
                =
                cat_el_map_el_eq el (assoc' s t (identity _))
                · cat_el_map_pb_mor el s (t · identity _)
                · cat_el_map_mor el (t · identity _))
          as p.
        {
          cbn.
          refine (!_).
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes (cat_stable_el_map_pb el s _)).
          }
          cbn.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply cat_el_map_mor_eq.
        }        etrans.
        {
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          exact (!p).
        }
        rewrite !assoc.
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr2 P).
    Qed.

    Definition cat_el_map_coherent_to_mor_to_el_map
      : cat_stable_el_map_coherent_from_mor (cat_el_map_mor el (identity _)) = el.
    Proof.
      use cat_el_map_eq.
      - intros Γ t.
        exact (z_iso_comp
                 (mor_to_cat_el_map_to_mor_z_iso t)
                 (cat_el_map_el_eq el (id_right _))).
      - intros Γ t.
        exact (mor_to_cat_el_map_to_mor_eq1 t).
      - intros Γ Δ s t.
        refine (_ @ mor_to_cat_el_map_to_mor_eq2 s t).
        apply assoc.
    Qed.

  End UniverseToMorphismToUniverse.

  Section MorphismToUniverseToMorphism.
    Context {e : C}
            (p : e --> univ_cat_universe C).

    Definition cat_el_map_to_mor_to_map_z_iso_inv
      : e --> pullbacks_univ_cat_with_finlim C _ _ _ p (identity _).
    Proof.
      use PullbackArrow.
      - apply identity.
      - exact p.
      - abstract
          (rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition cat_el_map_to_mor_to_map_z_iso_invs
      : is_inverse_in_precat
          (PullbackPr1 _)
          cat_el_map_to_mor_to_map_z_iso_inv.
    Proof.
      unfold cat_el_map_to_mor_to_map_z_iso_inv.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left, id_right.
          apply idpath.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          refine (PullbackSqrCommutes _ @ _).
          apply id_right.
      - apply PullbackArrow_PullbackPr1.
    Qed.

    Definition cat_el_map_to_mor_to_map_z_iso
      : z_iso
          (pullbacks_univ_cat_with_finlim
             C
             _ _ _
             p
             (identity _))
          e.
    Proof.
      use make_z_iso.
      - exact (PullbackPr1 _).
      - exact cat_el_map_to_mor_to_map_z_iso_inv.
      - exact cat_el_map_to_mor_to_map_z_iso_invs.
    Defined.
  End MorphismToUniverseToMorphism.

  Proposition mor_to_cat_el_map_to_mor
              (ep : ∑ (e : C), e --> univ_cat_universe C)
    : cat_stable_el_map_coherent_to_mor (cat_stable_el_map_coherent_from_mor (pr2 ep)) = ep.
  Proof.
    induction ep as [ e p ].
    use total2_paths_f.
    - use isotoid.
      {
        apply univalent_category_is_univalent.
      }
      exact (cat_el_map_to_mor_to_map_z_iso p).
    - abstract
        (cbn ;
         rewrite transportf_isotoid ;
         cbn ;
         unfold cat_el_map_to_mor_to_map_z_iso_inv ;
         apply PullbackArrow_PullbackPr2).
  Qed.

  (** * 4. The equivalence between morphisms and universes *)
  Definition cat_stable_el_map_coherent_mor_weq
    : cat_stable_el_map_coherent C
      ≃
      ∑ (e : C), e --> univ_cat_universe C.
  Proof.
    use weq_iso.
    - exact cat_stable_el_map_coherent_to_mor.
    - exact (λ ep, cat_stable_el_map_coherent_from_mor (pr2 ep)).
    - intros el.
      exact (cat_el_map_coherent_to_mor_to_el_map el).
    - intros ep.
      exact (mor_to_cat_el_map_to_mor ep).
  Defined.
End UniverseAsMorphism.
