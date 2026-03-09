(**

 Internal equivalence relations in the slice category

 A regular category is said to be exact if every internal equivalence relation is
 effective, which implies, among others, that it has a coequalizer. In this file, we
 study internal equivalence relations in slice categories. More specific, we show that
 internal equivalence relations in the slice category correspond to a more type theoretic
 notion of equivalence relation.

 To understand this type theoretic notion, we look at the comprehension category arising
 from the codomain fibration. In this fibration, propositions in context `Γ` correspond to
 monomorphisms into `Γ`. If `A` is a type in context `Γ`(i.e., we have a morphism
 `π : A --> Γ`), then a relation on `A` corresponds to a monomorphism into the pullback of
 `π` with `π`. This is different from an internal relation, which is defined to be a jointly
 monic span. We show that the type theoretic notion of relation corresponds to the usual
 internal notion of relation. In addition, we define when a type theoretic relation is an
 equivalence relation, and we show that type theoretic equivalence relations correspond to
 internal equivalence relations defined via spans.

 Contents
 1. Internal relations (defined in a type theoretic style)
 2. Properties of such relations
 3. Type theoretic equivalence relations
 4. Internal relations in the internal and type theoretic style correspond
 5. Correspondence in their provability
 6. Correspondence for properties of internal relations
 7. Correspondence for internal equivalence relations
 8. Quotients of internal equivalence relations (type theoretic style)

                                                                                       *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRegular.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

Section InternalTypeRel.
  Context {C : category}
          {PB : Pullbacks C}
          {Γ A : C}
          {π : A --> Γ}.

  (** * 1. Internal relations (defined in a type theoretic style) *)
  Definition internal_type_rel
    : UU
    := ∑ (r : C), Monic _ r (PB _ _ _ π π).

  Definition make_internal_type_rel
             (r : C)
             (m : Monic _ r (PB _ _ _ π π))
    : internal_type_rel
    := r ,, m.

  Coercion internal_type_rel_to_ty
           (r : internal_type_rel)
    : C
    := pr1 r.

  Definition internal_type_rel_monic
             (r : internal_type_rel)
    : Monic _ r (PB _ _ _ π π)
    := pr2 r.

  Definition path_internal_type_rel_help
             {r₁ r₂ : internal_type_rel}
             (p : (r₁ : C) = r₂)
             (q : idtoiso p · internal_type_rel_monic r₂
                  =
                  internal_type_rel_monic r₁)
    : r₁ = r₂.
  Proof.
    induction r₁ as [ r₁ M₁ ].
    induction r₂ as [ r₂ M₂ ].
    cbn in *.
    induction p.
    apply maponpaths.
    cbn in q.
    rewrite id_left in q.
    use Monic_eq.
    exact (!q).
  Qed.

  Definition path_internal_type_rel
             (HC : is_univalent C)
             {r₁ r₂ : internal_type_rel}
             (p : z_iso r₁ r₂)
             (q : p · internal_type_rel_monic r₂
                  =
                  internal_type_rel_monic r₁)
    : r₁ = r₂.
  Proof.
    use path_internal_type_rel_help.
    - exact (isotoid C HC p).
    - rewrite idtoiso_isotoid.
      exact q.
  Qed.

  (**
     The function [subst_rel] allows us to instantiate a type theoretic relation
     with two concrete terms.
   *)
  Definition subst_rel
             {Δ : C}
             {s : Δ --> Γ}
             (t₁ t₂ : section_of_mor (PullbackPr2 (PB _ _ _ π s)))
    : Δ --> PB _ _ _ π π.
  Proof.
    use PullbackArrow.
    - exact (pr1 t₁ · PullbackPr1 _).
    - exact (pr1 t₂ · PullbackPr1 _).
    - abstract
        (rewrite !assoc' ;
         rewrite PullbackSqrCommutes ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         refine (section_of_mor_eq t₁ @ _) ;
         refine (!_) ;
         apply (section_of_mor_eq t₂)).
  Defined.

  Definition internal_type_rel_prf
             (r : internal_type_rel)
             {Δ : C}
             {s : Δ --> Γ}
             (t₁ t₂ : section_of_mor (PullbackPr2 (PB _ _ _ π s)))
    : UU
    := section_of_mor
         (PullbackPr2
            (PB _ _ _ (internal_type_rel_monic r) (subst_rel t₁ t₂))).

  Identity Coercion prf_to_tm : internal_type_rel_prf >-> section_of_mor.

  (** * 2. Properties of such relations *)
  Definition internal_type_rel_isrefl
             (r : internal_type_rel)
    : UU
    := ∏ (Δ : C)
         (s : Δ --> Γ)
         (t : section_of_mor (PullbackPr2 (PB _ _ _ π s))),
       internal_type_rel_prf r t t.

  Proposition isaprop_internal_type_rel_isrefl
              (r : internal_type_rel)
    : isaprop (internal_type_rel_isrefl r).
  Proof.
    use invproofirrelevance.
    intros refl₁ refl₂.
    use funextsec ; intro Δ.
    use funextsec ; intro s.
    use funextsec ; intro t.
    use eq_section_of_mor.
    cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - use (MonicisMonic _ (internal_type_rel_monic r) _).
      rewrite !assoc'.
      rewrite PullbackSqrCommutes.
      rewrite !assoc.
      apply maponpaths_2.
      exact (section_of_mor_eq _ @ !(section_of_mor_eq _)).
    - exact (section_of_mor_eq _ @ !(section_of_mor_eq _)).
  Qed.

  Definition internal_type_rel_issymm
             (r : internal_type_rel)
    : UU
    := ∏ (Δ : C)
         (s : Δ --> Γ)
         (t₁ t₂ : section_of_mor (PullbackPr2 (PB _ _ _ π s))),
       internal_type_rel_prf r t₁ t₂
       →
       internal_type_rel_prf r t₂ t₁.

  Proposition isaprop_internal_type_rel_issymm
              (r : internal_type_rel)
    : isaprop (internal_type_rel_issymm r).
  Proof.
    use invproofirrelevance.
    intros sym₁ sym₂.
    use funextsec ; intro Δ.
    use funextsec ; intro s.
    use funextsec ; intro t₁.
    use funextsec ; intro t₂.
    use funextsec ; intro p.
    use eq_section_of_mor.
    cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - use (MonicisMonic _ (internal_type_rel_monic r) _).
      rewrite !assoc'.
      rewrite PullbackSqrCommutes.
      rewrite !assoc.
      apply maponpaths_2.
      exact (section_of_mor_eq _ @ !(section_of_mor_eq _)).
    - exact (section_of_mor_eq _ @ !(section_of_mor_eq _)).
  Qed.

  Definition internal_type_rel_istrans
             (r : internal_type_rel)
    : UU
    := ∏ (Δ : C)
         (s : Δ --> Γ)
         (t₁ t₂ t₃ : section_of_mor (PullbackPr2 (PB _ _ _ π s))),
       internal_type_rel_prf r t₁ t₂
       →
       internal_type_rel_prf r t₂ t₃
       →
       internal_type_rel_prf r t₁ t₃.

  Proposition isaprop_internal_type_rel_istrans
              (r : internal_type_rel)
    : isaprop (internal_type_rel_istrans r).
  Proof.
    use invproofirrelevance.
    intros trans₁ trans₂.
    use funextsec ; intro Δ.
    use funextsec ; intro s.
    use funextsec ; intro t₁.
    use funextsec ; intro t₂.
    use funextsec ; intro t₃.
    use funextsec ; intro p.
    use funextsec ; intro q.
    use eq_section_of_mor.
    cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - use (MonicisMonic _ (internal_type_rel_monic r) _).
      rewrite !assoc'.
      rewrite PullbackSqrCommutes.
      rewrite !assoc.
      apply maponpaths_2.
      exact (section_of_mor_eq _ @ !(section_of_mor_eq _)).
    - exact (section_of_mor_eq _ @ !(section_of_mor_eq _)).
  Qed.

  (** * 3. Type theoretic equivalence relations *)
  Definition internal_type_rel_iseqrel
             (r : internal_type_rel)
    : UU
    := internal_type_rel_isrefl r
       ×
       internal_type_rel_issymm r
       ×
       internal_type_rel_istrans r.

  Proposition isaprop_internal_type_rel_iseqrel
              (r : internal_type_rel)
    : isaprop (internal_type_rel_iseqrel r).
  Proof.
    repeat use isapropdirprod.
    - apply isaprop_internal_type_rel_isrefl.
    - apply isaprop_internal_type_rel_issymm.
    - apply isaprop_internal_type_rel_istrans.
  Qed.

  Definition internal_type_eqrel
    : UU
    := ∑ (r : internal_type_rel), internal_type_rel_iseqrel r.

  Definition make_internal_type_eqrel
             (r : internal_type_rel)
             (Hr : internal_type_rel_iseqrel r)
    : internal_type_eqrel
    := r ,, Hr.

  Coercion internal_type_eqrel_to_internal_type_rel
           (r : internal_type_eqrel)
    : internal_type_rel
    := pr1 r.

  Proposition isrefl_internal_type_eqrel
              (r : internal_type_eqrel)
              {Δ : C}
              {s : Δ --> Γ}
              (t : section_of_mor (PullbackPr2 (PB _ _ _ π s)))
    : internal_type_rel_prf r t t.
  Proof.
    exact (pr12 r Δ s t).
  Defined.

  Proposition issymm_internal_type_eqrel
              (r : internal_type_eqrel)
              {Δ : C}
              {s : Δ --> Γ}
              {t₁ t₂ : section_of_mor (PullbackPr2 (PB _ _ _ π s))}
              (p : internal_type_rel_prf r t₁ t₂)
    : internal_type_rel_prf r t₂ t₁.
  Proof.
    exact (pr122 r Δ s t₁ t₂ p).
  Defined.

  Proposition istrans_internal_type_eqrel
              (r : internal_type_eqrel)
              {Δ : C}
              {s : Δ --> Γ}
              {t₁ t₂ t₃ : section_of_mor (PullbackPr2 (PB _ _ _ π s))}
              (p : internal_type_rel_prf r t₁ t₂)
              (q : internal_type_rel_prf r t₂ t₃)
    : internal_type_rel_prf r t₁ t₃.
  Proof.
    exact (pr222 r Δ s t₁ t₂ t₃ p q).
  Defined.

  Proposition path_internal_type_eqrel
              (HC : is_univalent C)
              {r₁ r₂ : internal_type_eqrel}
              (p : z_iso r₁ r₂)
              (q : p · internal_type_rel_monic r₂
                   =
                   internal_type_rel_monic r₁)
    : r₁ = r₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_internal_type_rel_iseqrel.
    }
    use path_internal_type_rel.
    - exact HC.
    - exact p.
    - exact q.
  Qed.
End InternalTypeRel.

Arguments internal_type_rel {C} PB {Γ A} π.
Arguments internal_type_eqrel {C} PB {Γ A} π.

Section RelationVersusMono.
  Context {C : category}
          (PB : Pullbacks C)
          {Γ A : C}
          (π : A --> Γ)
          (Aπ := make_cod_fib_ob π : C/Γ).

  (** * 4. Internal relations in the internal and type theoretic style correspond *)
  Definition interal_relation_to_type_rel_ob
             (r : internal_relation Aπ)
    : cod_dom r --> PB Γ A A π π.
  Proof.
    use PullbackArrow.
    - exact (dom_mor (internal_relation_src r)).
    - exact (dom_mor (internal_relation_tar r)).
    - abstract
        (refine (mor_eq (internal_relation_src r) @ _) ;
         exact (!(mor_eq (internal_relation_tar r)))).
  Defined.

  Arguments interal_relation_to_type_rel_ob /.

  Proposition is_monic_interal_relation_to_type_rel_is_monic
              (r : internal_relation Aπ)
    : isMonic (interal_relation_to_type_rel_ob r).
  Proof.
    cbn.
    intros w g h p.
    use from_internal_relation_slice_monic.
    - refine (_ @ maponpaths (λ z, z · PullbackPr1 _) p @ _).
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
    - refine (_ @ maponpaths (λ z, z · PullbackPr2 _) p @ _).
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
  Qed.

  Definition monic_interal_relation_to_type_rel_monic
             (r : internal_relation Aπ)
    : Monic C (cod_dom r) (PB Γ A A π π).
  Proof.
    use make_Monic.
    - exact (interal_relation_to_type_rel_ob r).
    - exact (is_monic_interal_relation_to_type_rel_is_monic r).
  Defined.

  Definition interal_relation_to_type_rel
             (r : internal_relation Aπ)
    : internal_type_rel PB π.
  Proof.
    simple refine (_ ,, _).
    - exact (cod_dom r).
    - exact (monic_interal_relation_to_type_rel_monic r).
  Defined.

  Definition internal_type_rel_to_slice_rel_ob
             (r : internal_type_rel PB π)
    : C/Γ.
  Proof.
    use make_cod_fib_ob.
    - exact r.
    - exact (internal_type_rel_monic r · PullbackPr1 _ · π).
  Defined.

  Definition internal_type_rel_to_slice_rel_src
             (r : internal_type_rel PB π)
    : internal_type_rel_to_slice_rel_ob r --> Aπ.
  Proof.
    use make_cod_fib_mor.
    - exact (internal_type_rel_monic r · PullbackPr1 _).
    - apply idpath.
  Defined.

  Definition internal_type_rel_to_slice_rel_tar
             (r : internal_type_rel PB π)
    : internal_type_rel_to_slice_rel_ob r --> Aπ.
  Proof.
    use make_cod_fib_mor.
    - exact (internal_type_rel_monic r · PullbackPr2 _).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite PullbackSqrCommutes ;
         apply idpath).
  Defined.

  Proposition internal_type_rel_to_slice_rel_monic
              (r : internal_type_rel PB π)
              {w : C/Γ}
              {f g : w --> internal_type_rel_to_slice_rel_ob r}
              (p : f · internal_type_rel_to_slice_rel_src r
                   =
                   g · internal_type_rel_to_slice_rel_src r)
              (q : f · internal_type_rel_to_slice_rel_tar r
                   =
                   g · internal_type_rel_to_slice_rel_tar r)
    : f = g.
  Proof.
    use eq_mor_cod_fib.
    use (MonicisMonic _ (internal_type_rel_monic r)).
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (PB Γ A A π π))).
    - pose (maponpaths dom_mor p) as p'.
      rewrite !comp_in_cod_fib in p'.
      cbn in p'.
      rewrite !assoc'.
      exact p'.
    - pose (maponpaths dom_mor q) as q'.
      rewrite !comp_in_cod_fib in q'.
      cbn in q'.
      rewrite !assoc'.
      exact q'.
  Qed.

  Definition internal_type_rel_to_slice_rel
             (r : internal_type_rel PB π)
    : internal_relation Aπ.
  Proof.
    use make_internal_relation.
    - exact (internal_type_rel_to_slice_rel_ob r).
    - exact (internal_type_rel_to_slice_rel_src r).
    - exact (internal_type_rel_to_slice_rel_tar r).
    - exact (λ w f g p q, internal_type_rel_to_slice_rel_monic r p q).
  Defined.

  Context (HC : is_univalent C).

  Let CC : univalent_category := make_univalent_category C HC.

  Proposition internal_relation_to_type_rel_to_relation
              (r : internal_relation Aπ)
    : internal_type_rel_to_slice_rel (interal_relation_to_type_rel r)
      =
      r.
  Proof.
    use path_internal_relation.
    - apply (is_univalent_cod_slice (C := CC)).
    - simple refine (_ ,, _).
      + use make_cod_fib_mor.
        * apply identity.
        * abstract
            (cbn ;
             rewrite PullbackArrow_PullbackPr1 ;
             rewrite id_left ;
             exact (!(mor_eq (internal_relation_src r)))).
      + use make_is_z_iso_in_slice.
        apply is_z_isomorphism_identity.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib ; cbn.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_left.
      apply idpath.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib ; cbn.
      rewrite PullbackArrow_PullbackPr2.
      rewrite id_left.
      apply idpath.
  Qed.

  Proposition internal_type_rel_to_slice_rel_to_type_rel
              (r : internal_type_rel PB π)
    : interal_relation_to_type_rel (internal_type_rel_to_slice_rel r)
      =
      r.
  Proof.
    use path_internal_type_rel.
    - exact HC.
    - apply identity_z_iso.
    - cbn.
      rewrite id_left.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (PB Γ A A π π))).
      + rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite PullbackArrow_PullbackPr2.
        apply idpath.
  Qed.

  Definition internal_slice_rel_weq_internal_type_rel
    : internal_relation Aπ ≃ internal_type_rel PB π.
  Proof.
    use weq_iso.
    - exact interal_relation_to_type_rel.
    - exact internal_type_rel_to_slice_rel.
    - exact internal_relation_to_type_rel_to_relation.
    - exact internal_type_rel_to_slice_rel_to_type_rel.
  Defined.

  (** * 5. Correspondence in their provability *)
  Definition subst_to_slice_ob_internal_rel
             (r : internal_relation Aπ)
             {Δ : C}
             (s : Δ --> Γ)
    : C/Γ
    := make_cod_fib_ob s.

  Definition tm_to_slice_mor
             (r : internal_relation Aπ)
             {Δ : C}
             {s : Δ --> Γ}
             (t : section_of_mor (PullbackPr2 (PB Γ A Δ π s)))
    : subst_to_slice_ob_internal_rel r s --> Aπ.
  Proof.
    use make_cod_fib_mor.
    - exact (t · PullbackPr1 _).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite PullbackSqrCommutes ;
         rewrite !assoc ;
         refine (_ @ id_left _) ;
         apply maponpaths_2 ;
         apply section_of_mor_eq).
  Defined.

  Section ToPrfRelation.
    Context (r : internal_relation Aπ)
            {Δ : C}
            {s : Δ --> Γ}
            {t₁ t₂ : section_of_mor (PullbackPr2 (PB Γ A Δ π s))}
            (p : internal_type_rel_prf (interal_relation_to_type_rel r) t₁ t₂).

    Definition prf_to_internal_relation_dom_mor
      : cod_dom (subst_to_slice_ob_internal_rel r s) --> cod_dom r
      := p · PullbackPr1 _.

    Arguments prf_to_internal_relation_dom_mor /.

    Proposition prf_to_internal_relation_mor_eq
      : prf_to_internal_relation_dom_mor · cod_mor r
        =
        cod_mor (subst_to_slice_ob_internal_rel r s).
    Proof.
      cbn.
      etrans.
      {
        apply maponpaths.
        exact (!(mor_eq (internal_relation_src r))).
      }
      cbn.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (_ @ maponpaths (λ z, z · PullbackPr1 _) (PullbackSqrCommutes _)).
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      }
      unfold subst_rel.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite assoc'.
        rewrite PullbackSqrCommutes.
        rewrite assoc.
        apply maponpaths_2.
        apply section_of_mor_eq.
      }
      rewrite id_left.
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply section_of_mor_eq.
    Qed.

    Definition prf_to_internal_relation_mor
      : subst_to_slice_ob_internal_rel r s --> r.
    Proof.
      use make_cod_fib_mor.
      - exact prf_to_internal_relation_dom_mor.
      - exact prf_to_internal_relation_mor_eq.
    Defined.

    Proposition prf_to_internal_relation_src
      : prf_to_internal_relation_mor · internal_relation_src r
        =
        tm_to_slice_mor r t₁.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        refine (_ @ maponpaths (λ z, z · PullbackPr1 _) (PullbackSqrCommutes _)).
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      }
      unfold subst_rel.
      rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply section_of_mor_eq.
      }
      rewrite id_left.
      apply idpath.
    Qed.

    Proposition prf_to_internal_relation_tar
      : prf_to_internal_relation_mor · internal_relation_tar r
        =
        tm_to_slice_mor r t₂.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        refine (_ @ maponpaths (λ z, z · PullbackPr2 _) (PullbackSqrCommutes _)).
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
      }
      unfold subst_rel.
      rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply section_of_mor_eq.
      }
      rewrite id_left.
      apply idpath.
    Qed.

    Definition prf_to_internal_relation
      : internal_relation_to_arr_hrel
          r
          (subst_to_slice_ob_internal_rel r s)
          (tm_to_slice_mor r t₁)
          (tm_to_slice_mor r t₂).
    Proof.
      simple refine (_ ,, _).
      - exact prf_to_internal_relation_mor.
      - split.
        + exact prf_to_internal_relation_src.
        + exact prf_to_internal_relation_tar.
    Defined.
  End ToPrfRelation.

  Section FromPrfRelation.
    Context (r : internal_relation Aπ)
            {Δ : C}
            {s : Δ --> Γ}
            {t₁ t₂ : section_of_mor (PullbackPr2 (PB Γ A Δ π s))}
            (p : internal_relation_to_arr_hrel
                   r
                   (subst_to_slice_ob_internal_rel r s)
                   (tm_to_slice_mor r t₁)
                   (tm_to_slice_mor r t₂)).

    Let prf : subst_to_slice_ob_internal_rel r s --> r := pr1 p.

    Proposition internal_relation_to_prf_eq
      : dom_mor prf · internal_type_rel_monic (interal_relation_to_type_rel r)
        =
        identity Δ · subst_rel t₁ t₂.
    Proof.
      rewrite id_left.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - unfold subst_rel, internal_type_rel_monic ; cbn.
        rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        refine (_ @ maponpaths dom_mor (pr12 p)).
        rewrite comp_in_cod_fib.
        apply idpath.
      - unfold subst_rel, internal_type_rel_monic ; cbn.
        rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        refine (_ @ maponpaths dom_mor (pr22 p)).
        rewrite comp_in_cod_fib.
        apply idpath.
    Qed.

    Definition internal_relation_to_prf
      : internal_type_rel_prf (interal_relation_to_type_rel r) t₁ t₂.
    Proof.
      use make_section_of_mor.
      - use PullbackArrow.
        + exact (dom_mor prf).
        + apply identity.
        + apply internal_relation_to_prf_eq.
      - apply PullbackArrow_PullbackPr2.
    Defined.
  End FromPrfRelation.

  Definition slice_mor_to_tm
             (r : internal_type_rel PB π)
             {Δs : C/Γ}
             (t : Δs --> Aπ)
    : section_of_mor (PullbackPr2 (PB Γ A _ π (cod_mor Δs))).
  Proof.
    use make_section_of_mor.
    - use PullbackArrow.
      + exact (dom_mor t).
      + apply identity.
      + abstract
          (rewrite id_left ;
           exact (mor_eq t)).
    - apply PullbackArrow_PullbackPr2.
  Defined.

  Section ToPrfTypeRelation.
    Context {r : internal_type_rel PB π}
            {Δs : C/Γ}
            {t₁ t₂ : Δs --> Aπ}
            (p : internal_type_rel_prf
                   r
                   (slice_mor_to_tm r t₁)
                   (slice_mor_to_tm r t₂)).

    Definition internal_type_rel_from_prf_mor
      : Δs --> internal_type_rel_to_slice_rel r.
    Proof.
      use make_cod_fib_mor.
      - exact (pr1 p · PullbackPr1 _).
      - abstract
          (cbn ;
           rewrite !assoc' ;
           rewrite PullbackSqrCommutes ;
           rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
           rewrite PullbackSqrCommutes ;
           rewrite !assoc ;
           etrans ;
           [ do 3 apply maponpaths_2 ;
             apply section_of_mor_eq
           | ] ;
           rewrite id_left ;
           unfold subst_rel ;
           rewrite PullbackArrow_PullbackPr2 ; cbn ;
           rewrite PullbackArrow_PullbackPr1 ;
           apply (mor_eq t₂)).
    Defined.

    Proposition internal_type_rel_from_prf_src
      : internal_type_rel_from_prf_mor
        · internal_relation_src (internal_type_rel_to_slice_rel r)
        =
        t₁.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite PullbackSqrCommutes.
        rewrite !assoc'.
        unfold subst_rel.
        rewrite PullbackArrow_PullbackPr1.
        cbn.
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply section_of_mor_eq.
      }
      apply id_left.
    Qed.

    Proposition internal_type_rel_from_prf_tar
      : internal_type_rel_from_prf_mor
        · internal_relation_tar (internal_type_rel_to_slice_rel r)
        =
        t₂.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite PullbackSqrCommutes.
        rewrite !assoc'.
        unfold subst_rel.
        rewrite PullbackArrow_PullbackPr2.
        cbn.
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply section_of_mor_eq.
      }
      apply id_left.
    Qed.

    Definition internal_type_rel_from_prf
      : internal_relation_to_arr_hrel (internal_type_rel_to_slice_rel r) Δs t₁ t₂.
    Proof.
      refine (internal_type_rel_from_prf_mor ,, _ ,, _).
      - exact internal_type_rel_from_prf_src.
      - exact internal_type_rel_from_prf_tar.
    Defined.
  End ToPrfTypeRelation.

  Section FromPrfTypeRelation.
    Context {r : internal_type_rel PB π}
            {Δs : C/Γ}
            {t₁ t₂ : Δs --> Aπ}
            (p : internal_relation_to_arr_hrel
                   (internal_type_rel_to_slice_rel r)
                   Δs
                   t₁
                   t₂).

    Proposition prf_from_internal_type_rel_mor_eq
      : dom_mor (pr1 p) · internal_type_rel_monic r
        =
        identity _ · subst_rel (slice_mor_to_tm r t₁) (slice_mor_to_tm r t₂).
    Proof.
      rewrite id_left.
      unfold subst_rel.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - cbn.
        rewrite !PullbackArrow_PullbackPr1.
        rewrite !assoc'.
        refine (_ @ maponpaths dom_mor (pr12 p)).
        rewrite comp_in_cod_fib.
        cbn.
        apply idpath.
      - cbn.
        rewrite PullbackArrow_PullbackPr2.
        rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc'.
        refine (_ @ maponpaths dom_mor (pr22 p)).
        rewrite comp_in_cod_fib.
        cbn.
        apply idpath.
    Qed.

    Definition prf_from_internal_type_rel_mor
      : cod_dom Δs
        -->
        PB (PB Γ A A π π) r (cod_dom Δs)
           (internal_type_rel_monic r)
           (subst_rel (slice_mor_to_tm r t₁) (slice_mor_to_tm r t₂)).
    Proof.
      use PullbackArrow.
      - exact (dom_mor (pr1 p)).
      - apply identity.
      - exact prf_from_internal_type_rel_mor_eq.
    Defined.

    Definition prf_from_internal_type_rel
      : internal_type_rel_prf
          r
          (slice_mor_to_tm r t₁)
          (slice_mor_to_tm r t₂).
    Proof.
      use make_section_of_mor.
      - apply prf_from_internal_type_rel_mor.
      - abstract
          (apply PullbackArrow_PullbackPr2).
    Defined.
  End FromPrfTypeRelation.

  (** * 6. Correspondence for properties of internal relations *)
  Proposition is_refl_slice_rel_to_refl_type_rel
              {r : internal_relation Aπ}
              (Hr : internal_isrefl r)
    : internal_type_rel_isrefl (interal_relation_to_type_rel r).
  Proof.
    intros Δ s t.
    use internal_relation_to_prf.
    apply Hr.
  Defined.

  Proposition is_refl_type_rel_to_refl_slice_rel
              {r : internal_type_rel PB π}
              (Hr : internal_type_rel_isrefl r)
    : internal_isrefl (internal_type_rel_to_slice_rel r).
  Proof.
    intros Δs t.
    use internal_type_rel_from_prf.
    apply Hr.
  Defined.

  Proposition is_symm_slice_rel_to_symm_type_rel
              {r : internal_relation Aπ}
              (Hr : internal_issymm r)
    : internal_type_rel_issymm (interal_relation_to_type_rel r).
  Proof.
    intros Δ s t₁ t₂ p.
    use internal_relation_to_prf.
    apply Hr.
    use prf_to_internal_relation.
    apply p.
  Defined.

  Proposition is_symm_type_rel_to_symm_slice_rel
              {r : internal_type_rel PB π}
              (Hr : internal_type_rel_issymm r)
    : internal_issymm (internal_type_rel_to_slice_rel r).
  Proof.
    intros Δs t₁ t₂ p.
    use internal_type_rel_from_prf.
    apply Hr.
    use prf_from_internal_type_rel.
    apply p.
  Defined.

  Proposition is_trans_slice_rel_to_trans_type_rel
              {r : internal_relation Aπ}
              (Hr : internal_istrans r)
    : internal_type_rel_istrans (interal_relation_to_type_rel r).
  Proof.
    intros Δ s t₁ t₂ t₃ p q.
    use internal_relation_to_prf.
    use Hr.
    - exact (tm_to_slice_mor r t₂).
    - use prf_to_internal_relation.
      apply p.
    - use prf_to_internal_relation.
      apply q.
  Defined.

  Proposition is_trans_type_rel_to_trans_slice_rel
              {r : internal_type_rel PB π}
              (Hr : internal_type_rel_istrans r)
    : internal_istrans (internal_type_rel_to_slice_rel r).
  Proof.
    intros Δs t₁ t₂ t₃ p q.
    use internal_type_rel_from_prf.
    use Hr.
    - exact (slice_mor_to_tm r t₂).
    - use prf_from_internal_type_rel.
      apply p.
    - use prf_from_internal_type_rel.
      apply q.
  Defined.

  (** * 7. Correspondence for internal equivalence relations *)
  Definition internal_slice_eqrel_to_internal_type_eqrel
             (r : internal_eqrel Aπ)
    : internal_type_eqrel PB π.
  Proof.
    use make_internal_type_eqrel.
    - exact (interal_relation_to_type_rel r).
    - repeat split.
      + apply is_refl_slice_rel_to_refl_type_rel.
        apply r.
      + apply is_symm_slice_rel_to_symm_type_rel.
        apply r.
      + apply is_trans_slice_rel_to_trans_type_rel.
        apply r.
  Defined.

  Definition internal_type_eqrel_to_internal_slice_eqrel
             (r : internal_type_eqrel PB π)
    : internal_eqrel Aπ.
  Proof.
    use make_internal_eqrel.
    - exact (internal_type_rel_to_slice_rel r).
    - repeat split.
      + apply is_refl_type_rel_to_refl_slice_rel.
        apply r.
      + apply is_symm_type_rel_to_symm_slice_rel.
        apply r.
      + apply is_trans_type_rel_to_trans_slice_rel.
        apply r.
  Defined.

  Definition internal_slice_eqrel_weq_internal_type_eqrel
    : internal_eqrel Aπ ≃ internal_type_eqrel PB π.
  Proof.
    use weq_iso.
    - exact internal_slice_eqrel_to_internal_type_eqrel.
    - exact internal_type_eqrel_to_internal_slice_eqrel.
    - abstract
        (intro r ;
         use subtypePath ; [ intro ; apply isaprop_internal_iseqrel | ] ;
         apply internal_relation_to_type_rel_to_relation).
    - abstract
        (intro r ;
         use subtypePath ; [ intro ; apply isaprop_internal_type_rel_iseqrel | ] ;
         apply internal_type_rel_to_slice_rel_to_type_rel).
  Defined.
End RelationVersusMono.

(** * 8. Quotients of internal equivalence relations (type theoretic style) *)
Definition quot_internal_type_eqrel
           {C : category}
           (HC : is_exact C)
           (PB : Pullbacks C)
           {Γ A : C}
           {π : A --> Γ}
           (r : internal_type_eqrel PB π)
  : Coequalizer
      (internal_relation_src (internal_type_eqrel_to_internal_slice_eqrel PB π r))
      (internal_relation_tar (internal_type_eqrel_to_internal_slice_eqrel PB π r))
  := quotient_internal_eqrel
       (is_exact_disp_cod HC Γ)
       (internal_type_eqrel_to_internal_slice_eqrel PB π r).

Proposition is_regular_epi_quot_internal_type_eqrel
            {C : category}
            (HC : is_exact C)
            (PB : Pullbacks C)
            {Γ A : C}
            {π : A --> Γ}
            (r : internal_type_eqrel PB π)
  : is_regular_epi (CoequalizerArrow (quot_internal_type_eqrel HC PB r)).
Proof.
  use hinhpr.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (internal_type_eqrel_to_internal_slice_eqrel PB π r).
  - exact (internal_relation_src (internal_type_eqrel_to_internal_slice_eqrel PB π r)).
  - exact (internal_relation_tar (internal_type_eqrel_to_internal_slice_eqrel PB π r)).
  - apply CoequalizerEqAr.
  - apply isCoequalizer_Coequalizer.
Defined.
