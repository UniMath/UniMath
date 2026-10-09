(**

 The adjoint equivalence between H-valued sets and sheaves

 To finish the proof that the topos of sheaves on a complete Heyting algebra `H`
 and H-valued sets are equivalent, we show that the functor from sheaves to H-valued
 sets is essentially surjective. Concretely, we construct the sheafification of
 each H-valued set `X`, and we show that the H-valued set associated to the
 sheafification iss isomorphic to `X`. Note the difference with the sheafification
 of presheaves, because presheaves are not necessarily isomorphic to their
 sheafifications.

 If we have an H-valued set `(X, ~)`, then we construct its sheafification as the
 sheaf of all singletons, where a singleton is defined to be a function `f` from
 `X` to `H` such that
 - If `f x` and `x ~ y`, then `f y` (i.e., `f` respects equality)
 - If `f x` and `f y`, then `x ~ y` (i.e., `f` is a singleton)
 In essence, `f` represents a predicate on `X` valued in `H` and that predicate is
 a singleton. We also keep track of the extent: we have `ω : H`, and we require
 - We have `f x ≤ ω`
 - We have `ω ≤ \/_{ x : X } (f x)`
 The reason for keeping track of the extent, is so that we can nicely construct the
 corresponding sheaf: we have the construct the set of singletons on `X` for each
 `ω : H`, which represents the extent of the singleton.

 Content
 1. Singletons in an H-valued set
 2. The sheaf arising from an H-valued set
 2.1. The presheaf
 2.2. The sheaf condition
 3. The isomorphism
 4. Split essential surjectivity and the adjoint equivalence

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.OrderTheory.Lattice.DerivedLawsCompleteHeyting.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ExamplesSites.
Require Import UniMath.CategoryTheory.Presheaves.SheafToHValuedSet.
Require Import UniMath.CategoryTheory.Presheaves.SheafToHValuedSetFF.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HValuedSets.

Local Open Scope heyting.
Local Open Scope cat.

Section SheafToHValuedSetEso.
  Context {H : complete_heyting_algebra}.

  Let C : site := cha_to_site H.

  (** * 1. Singletons in an H-valued set *)
  Definition is_singleton_h_valued_set
             {X : h_valued_set H}
             (f : X → H)
             (ω : H)
    : hProp
    := hconj
         (∀ (x y : X), (f x ∧ (x ~_{X} y)) ≤ f y)
         (hconj
            (∀ (x y : X), (f x ∧ f y) ≤ (x ~_{X} y))
            (hconj
               (∀ (x : X), f x ≤ ω)
               (ω ≤ \/_{ x : X } (f x)))).

  Definition singleton_h_valued_set
             (X : h_valued_set H)
             (ω : H)
    : UU
    := ∑ (f : X → H), is_singleton_h_valued_set f ω.

  Definition make_singleton_h_valued_set
             {X : h_valued_set H}
             {ω : H}
             (f : X → H)
             (Hf : is_singleton_h_valued_set f ω)
    : singleton_h_valued_set X ω
    := f ,, Hf.

  Definition singleton_h_valued_set_fun
             {X : h_valued_set H}
             {ω : H}
             (f : singleton_h_valued_set X ω)
    : X → H
    := pr1 f.

  Coercion singleton_h_valued_set_fun : singleton_h_valued_set >-> Funclass.

  Proposition singleton_h_valued_set_on_eq
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
              (x y : X)
    : (f x ∧ (x ~_{X} y)) ≤ f y.
  Proof.
    exact (pr12 f x y).
  Qed.

  Proposition singleton_h_valued_set_unique
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
              (x y : X)
    : (f x ∧ f y) ≤ (x ~_{X} y).
  Proof.
    exact (pr122 f x y).
  Qed.

  Proposition singleton_h_valued_set_extent_le
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
              (x : X)
    : f x ≤ ω.
  Proof.
    exact (pr1 (pr222 f) x).
  Qed.

  Proposition singleton_h_valued_set_extent
              {X : h_valued_set H}
              {ω : H}
              (f : singleton_h_valued_set X ω)
    : ω ≤ \/_{ x : X } (f x).
  Proof.
    exact (pr2 (pr222 f)).
  Qed.

  Proposition eq_singleton_h_valued_set
              {X : h_valued_set H}
              {ω : H}
              {f g : singleton_h_valued_set X ω}
              (p : ∏ (x : X), f x = g x)
    : f = g.
  Proof.
    use subtypePath_prop.
    use funextsec.
    exact p.
  Qed.

  Proposition isaset_singleton_h_valued_set
              (X : h_valued_set H)
              (ω : H)
    : isaset (singleton_h_valued_set X ω).
  Proof.
    use isaset_total2.
    - apply impred_isaset.
      intro.
      apply setproperty.
    - intros.
      apply isasetaprop.
      apply propproperty.
  Qed.

  Definition singleton_h_valued_set_hSet
             (X : h_valued_set H)
             (ω : H)
    : hSet
    := make_hSet
         (singleton_h_valued_set X ω)
         (isaset_singleton_h_valued_set X ω).

  Proposition el_to_singleton_h_valued_laws
              {X : h_valued_set H}
              (x : X)
    : is_singleton_h_valued_set (λ y, y ~_{X} x) (x ~_{X} x).
  Proof.
    repeat split.
    - intros y₁ y₂.
      refine (cha_le_trans _ (trans_per_of_h_valued_set H y₂ y₁ x)).
      rewrite cha_min_comm.
      use cha_and_monotone_l.
      use cha_eq_to_refl.
      exact (sym_per_of_h_valued_set H y₁ y₂).
    - intros y₁ y₂.
      refine (cha_le_trans _ (trans_per_of_h_valued_set H y₁ x y₂)).
      use cha_and_monotone_r.
      use cha_eq_to_refl.
      exact (sym_per_of_h_valued_set H y₂ x).
    - intro y.
      use refl_r_per_of_h_valued_set.
    - use cha_le_lub.
      {
        exact x.
      }
      cbn.
      apply cha_le_refl.
  Qed.

  Definition el_to_singleton_h_valued
             {X : h_valued_set H}
             (x : X)
    : singleton_h_valued_set X (x ~_{X} x).
  Proof.
    use make_singleton_h_valued_set.
    - exact (λ y, y ~_{X} x).
    - exact (el_to_singleton_h_valued_laws x).
  Defined.

  (** * 2. The sheaf arising from an H-valued set *)
  Section HValuedSetToSheaf.
    Context (X : h_valued_set H).

    (** * 2.1. The presheaf *)
    Proposition is_singleton_h_valued_set_le
                {ω₁ ω₂ : H}
                (p : ω₂ ≤ ω₁)
                (f : singleton_h_valued_set X ω₁)
      : is_singleton_h_valued_set (λ x, f x ∧ ω₂) ω₂.
    Proof.
      repeat split.
      - intros x y.
        use cha_min_le_case.
        + refine (cha_le_trans _ (singleton_h_valued_set_on_eq f x y)).
          use cha_min_le_case.
          * refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_min_le_l.
          * apply cha_min_le_r.
        + refine (cha_le_trans (cha_min_le_l _ _) _).
          apply cha_min_le_r.
      - intros x y.
        refine (cha_le_trans _ (singleton_h_valued_set_unique f x y)).
        use cha_min_le_case.
        + refine (cha_le_trans (cha_min_le_l _ _) _).
          apply cha_min_le_l.
        + refine (cha_le_trans (cha_min_le_r _ _) _).
          apply cha_min_le_l.
      - intro x.
        apply cha_min_le_r.
      - refine (cha_le_trans _ _).
        {
          use cha_eq_to_refl.
          exact (!(cha_min_le_eq_l p)).
        }
        refine (cha_le_trans _ _).
        {
          refine (cha_and_monotone_r _).
          exact (singleton_h_valued_set_extent f).
        }
        rewrite cha_frobenius.
        use cha_lub_le.
        intros x.
        cbn.
        use cha_le_lub.
        + exact x.
        + cbn.
          rewrite cha_min_comm.
          apply cha_le_refl.
    Qed.

    Definition singleton_h_valued_set_le
               {ω₁ ω₂ : H}
               (p : ω₂ ≤ ω₁)
               (f : singleton_h_valued_set X ω₁)
      : singleton_h_valued_set X ω₂.
    Proof.
      use make_singleton_h_valued_set.
      - exact (λ x, f x ∧ ω₂).
      - exact (is_singleton_h_valued_set_le p f).
    Defined.

    Definition h_valued_set_to_psh_data
      : functor_data C^op SET.
    Proof.
      use make_functor_data.
      - exact (λ (ω : H), singleton_h_valued_set_hSet X ω).
      - exact (λ (ω₁ ω₂ : H)
                 (p : ω₂ ≤ ω₁)
                 (f : singleton_h_valued_set X ω₁),
               singleton_h_valued_set_le p f).
    Defined.

    Proposition h_valued_set_to_psh_laws
      : is_functor h_valued_set_to_psh_data.
    Proof.
      split.
      - intros ω.
        use funextsec.
        intro f.
        cbn in ω, f.
        use eq_singleton_h_valued_set.
        cbn.
        intro x.
        use cha_min_le_eq_l.
        apply singleton_h_valued_set_extent_le.
      - intros ω₁ ω₂ ω₃ p q.
        cbn in ω₁, ω₂, ω₃, p, q.
        use funextsec.
        intro f.
        use eq_singleton_h_valued_set.
        cbn.
        intro x.
        rewrite cha_min_assoc.
        apply maponpaths.
        rewrite cha_min_comm.
        exact (!(cha_min_le_eq_l q)).
    Qed.

    Definition h_valued_set_to_psh
      : C^op ⟶ SET.
    Proof.
      use make_functor.
      - exact h_valued_set_to_psh_data.
      - exact h_valued_set_to_psh_laws.
    Defined.

    (** * 2.2. The sheaf condition *)
    Section SheafCondition.
      Context {ω : C}
              (P : sieve ω)
              (HP : C ω P)
              (z : matching_family h_valued_set_to_psh P).

      Definition matching_family_to_singleton
                 {y : H}
                 {f : y ≤ ω}
                 (p : P y f)
        : singleton_h_valued_set X y
        := pr1 z y f p.

      Proposition matching_family_to_singleton_eq
                  {y : H}
                  {f f' : y ≤ ω}
                  (p : P y f)
                  (p' : P y f')
        : matching_family_to_singleton p = matching_family_to_singleton p'.
      Proof.
        assert (r : f = f').
        {
          apply propproperty.
        }
        induction r.
        assert (r : p = p').
        {
          apply propproperty.
        }
        induction r.
        apply idpath.
      Qed.

      Proposition matching_family_to_singleton_restr
                  {ω₁ ω₂ : H}
                  (p₁ : ω₁ ≤ ω)
                  (p₂ : ω₂ ≤ ω₁)
                  (q₁ : P ω₂ (cha_le_trans p₂ p₁))
                  (q₂ : P ω₁ p₁)
                  (x : X)
        : (matching_family_to_singleton q₂ x ∧ ω₂) = matching_family_to_singleton q₁ x.
      Proof.
        exact (maponpaths
                 (λ h, pr1 h x)
                 (pr2 z _ _ (cha_le_trans p₂ p₁) p₁ p₂ (idpath _) q₁ q₂)).
      Qed.

      Let φ : X → H
        := λ x, \/_{ p : ∑ (y : H) (f : y ≤ ω), P y f }
                matching_family_to_singleton (pr22 p) x.

      Proposition h_valued_set_amalgamation_singleton_laws
        : is_singleton_h_valued_set φ ω.
      Proof.
        unfold φ.
        repeat split.
        - intros x y.
          rewrite cha_min_comm.
          rewrite cha_frobenius.
          use cha_lub_le.
          intros ( ω' & f & p ).
          cbn.
          use cha_le_lub.
          {
            exact (ω' ,, f ,, p).
          }
          cbn.
          rewrite cha_min_comm.
          apply singleton_h_valued_set_on_eq.
        - intros x y.
          rewrite cha_min_comm.
          rewrite cha_frobenius.
          use cha_lub_le.
          intros ( ω' & f & p ).
          cbn.
          rewrite cha_min_comm.
          rewrite cha_frobenius.
          use cha_lub_le.
          intros ( ω'' & f' & p' ).
          cbn.
          pose (ωm := ω' ∧ ω'').
          assert (pm : P ωm (cha_le_trans (cha_min_le_l _ _) f)).
          {
            refine (#ω P (cha_min_le_l _ _) _ p).
            apply idpath.
          }
          assert (pm' : P ωm (cha_le_trans (cha_min_le_r _ _) f')).
          {
            refine (#ω P (cha_min_le_l _ _) _ p).
            apply propproperty.
          }
          refine (cha_le_trans
                    _
                    (singleton_h_valued_set_unique (matching_family_to_singleton pm) x y)).
          assert ((matching_family_to_singleton pm x ∧ matching_family_to_singleton pm y)
                  =
                  (matching_family_to_singleton p x ∧ matching_family_to_singleton p' y ∧ ωm))
            as q.
          {
            etrans.
            {
              apply maponpaths_2.
              exact (!(matching_family_to_singleton_restr _ _ pm p x)).
            }
            rewrite cha_min_assoc.
            apply maponpaths.
            refine (!_).
            etrans.
            {
              apply maponpaths.
              exact (!(cha_min_id _)).
            }
            rewrite <- cha_min_assoc.
            refine (_ @ cha_min_comm _ _).
            apply maponpaths_2.
            refine (matching_family_to_singleton_restr _ _ pm' p' y @ _).
            apply maponpaths_2.
            apply matching_family_to_singleton_eq.
          }
          refine (cha_le_trans _ (cha_eq_to_refl (!q))).
          repeat use cha_min_le_case.
          + apply cha_min_le_l.
          + apply cha_min_le_r.
          + refine (cha_le_trans _ _).
            {
              refine (cha_and_monotone_l _).
              apply singleton_h_valued_set_extent_le.
            }
            apply cha_min_le_l.
          + refine (cha_le_trans _ _).
            {
              refine (cha_and_monotone_r _).
              apply singleton_h_valued_set_extent_le.
            }
            apply cha_min_le_r.
        - intro x.
          use cha_lub_le.
          intros ( ω' & f & p ).
          cbn.
          exact (cha_le_trans (singleton_h_valued_set_extent_le _ _) f).
        - refine (cha_le_trans HP _).
          use cha_lub_le.
          intros ( ω' & f & p ).
          cbn.
          refine (cha_le_trans
                    (singleton_h_valued_set_extent (matching_family_to_singleton p))
                    _).
          use cha_lub_le.
          intro x.
          use cha_le_lub.
          {
            exact x.
          }
          cbn.
          use cha_le_lub.
          {
            exact (ω' ,, f ,, p).
          }
          cbn.
          apply cha_le_refl.
      Qed.

      Definition h_valued_set_amalgamation_singleton
        : singleton_h_valued_set X ω.
      Proof.
        use make_singleton_h_valued_set.
        - exact φ.
        - exact h_valued_set_amalgamation_singleton_laws.
      Defined.

      Proposition h_valued_set_amalgamation_singleton_law
        : amalgamation_law z h_valued_set_amalgamation_singleton.
      Proof.
        intros ω' p Hp.
        cbn in ω', p, Hp ; cbn.
        use eq_singleton_h_valued_set.
        intro x.
        cbn.
        unfold φ.
        rewrite cha_min_comm.
        rewrite cha_frobenius.
        use cha_le_antisymm.
        - use cha_lub_le.
          intros ( ω'' & q & Hq ).
          cbn.
          rewrite cha_min_comm.
          pose (ωm := ω' ∧ ω'').
          assert (P ωm (cha_le_trans (cha_min_le_l _ _) p)) as rm.
          {
            simple refine (#ω P (cha_min_le_l _ _) _ Hp).
            apply idpath.
          }
          assert (P ωm (cha_le_trans (cha_min_le_r _ _) q)) as rm'.
          {
            simple refine (#ω P (cha_min_le_r _ _) _ Hq).
            apply idpath.
          }
          refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            apply maponpaths_2.
            exact (!(cha_min_le_eq_l (singleton_h_valued_set_extent_le _ _))).
          }
          rewrite cha_min_assoc.
          rewrite (cha_min_comm ω'' ω').
          refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            exact (matching_family_to_singleton_restr _ _ rm' Hq x).
          }
          refine (cha_le_trans _ (cha_min_le_l _ ωm)).
          use cha_eq_to_refl.
          refine (!_).
          etrans.
          {
            exact (matching_family_to_singleton_restr _ _ rm Hp x).
          }
          apply maponpaths_2.
          apply matching_family_to_singleton_eq.
        - use cha_le_lub.
          + exact (ω' ,, p ,, Hp).
          + cbn.
            use cha_min_le_case.
            * apply singleton_h_valued_set_extent_le.
            * apply cha_le_refl.
      Qed.

      Definition h_valued_set_amalgamation
        : amalgamation z.
      Proof.
        use make_amalgamation.
        - exact h_valued_set_amalgamation_singleton.
        - exact h_valued_set_amalgamation_singleton_law.
      Defined.

      Proposition h_valued_set_amalgamation_eq
                  (a : amalgamation z)
        : a = h_valued_set_amalgamation.
      Proof.
        use amalgamation_eq.
        use eq_singleton_h_valued_set.
        intro x.
        cbn.
        unfold φ.
        use cha_le_antisymm.
        - refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            exact (!(cha_min_le_eq_l (singleton_h_valued_set_extent_le (pr1 a) x))).
          }
          refine (cha_le_trans _ _).
          {
            refine (cha_and_monotone_r _).
            exact HP.
          }
          rewrite cha_frobenius.
          use cha_lub_le.
          intros i.
          use cha_le_lub.
          + exact i.
          + cbn.
            induction i as [ ω' [ f p ] ].
            cbn.
            unfold matching_family_to_singleton.
            use cha_eq_to_refl.
            exact (maponpaths (λ h, pr1 h x) (amalgamation_restr a f p)).
        - use cha_lub_le.
          intros ( ω' & f & p ).
          cbn.
          refine (cha_le_trans _ _).
          {
            use cha_eq_to_refl.
            exact (!(cha_min_le_eq_l (singleton_h_valued_set_extent_le _ x))).
          }
          refine (cha_le_trans
                    _
                    (cha_eq_to_refl
                       (cha_min_le_eq_l (singleton_h_valued_set_extent_le _ _)))).
          refine (cha_le_trans
                    _
                    (cha_and_monotone_r f)).
          pose proof (maponpaths
                        (λ h, pr1 h x)
                        (amalgamation_restr h_valued_set_amalgamation f p
                         @ !(amalgamation_restr a f p)))
            as q.
          cbn in q.
          refine (cha_le_trans _ (cha_eq_to_refl q)).
          use cha_and_monotone_l.
          use cha_le_lub.
          {
            exact (ω' ,, f ,, p).
          }
          cbn.
          apply cha_le_refl.
      Qed.
    End SheafCondition.

    Definition is_sheaf_h_valued_set_to_psh
      : is_sheaf h_valued_set_to_psh.
    Proof.
      intros ω P HP z.
      use make_iscontr.
      - exact (h_valued_set_amalgamation P HP z).
      - exact (h_valued_set_amalgamation_eq P HP z).
    Defined.

    Definition h_valued_set_to_sheaf
      : sheaf C.
    Proof.
      use make_sheaf.
      - exact h_valued_set_to_psh.
      - exact is_sheaf_h_valued_set_to_psh.
    Defined.

    (** * 3. The isomorphism *)
    Definition h_valued_set_to_sheaf_mor_rel
               {ω : H}
               (f : singleton_h_valued_set X ω)
               (x : X)
      : H
      := ω ∧ f x.

    Proposition h_valued_set_to_sheaf_mor_rel_dom
                {ω : H}
                (f : singleton_h_valued_set X ω)
                (x : X)
      : h_valued_set_to_sheaf_mor_rel f x
        ≤
        cha_sheaf_rel (F := h_valued_set_to_sheaf) f f.
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      use cha_le_lub.
      - refine (ω ,, cha_le_refl _ ,, cha_le_refl _ ,, _).
        use eq_singleton_h_valued_set.
        cbn.
        intro y.
        apply idpath.
      - cbn.
        apply cha_min_le_l.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_rel_cod
                {ω : H}
                (f : singleton_h_valued_set X ω)
                (x : X)
      : h_valued_set_to_sheaf_mor_rel f x
        ≤
        (x ~_{X} x).
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      refine (cha_le_trans _ (singleton_h_valued_set_unique f x x)).
      rewrite cha_min_id.
      apply cha_min_le_r.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_eq
                {ω₁ ω₂ : H}
                (f₁ : singleton_h_valued_set X ω₁)
                (f₂ : singleton_h_valued_set X ω₂)
                (x₁ x₂ : X)
      : (cha_sheaf_rel (F := h_valued_set_to_sheaf) f₁ f₂
         ∧ x₁ ~_{X} x₂
         ∧ h_valued_set_to_sheaf_mor_rel f₁ x₁)
        ≤
        h_valued_set_to_sheaf_mor_rel f₂ x₂.
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      unfold cha_sheaf_rel.
      rewrite cha_min_comm.
      rewrite cha_frobenius.
      use cha_lub_le.
      intros ( ωm & p & q & r ).
      cbn.
      rewrite !cha_min_assoc.
      refine (cha_le_trans _ _).
      {
        use cha_eq_to_refl.
        do 2 apply maponpaths.
        exact (maponpaths (λ h, pr1 h x₁) r).
      }
      cbn.
      use cha_min_le_case.
      - refine (cha_le_trans _ q).
        do 2 refine (cha_le_trans (cha_min_le_r _ _) _).
        exact (cha_min_le_r _ _).
      - refine (cha_le_trans _ _).
        + refine (cha_le_trans _ (singleton_h_valued_set_on_eq f₂ x₁ x₂)).
          use cha_min_le_case.
          * do 2 refine (cha_le_trans (cha_min_le_r _ _) _).
            apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_le_refl.
        + apply cha_le_refl.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_unique
                {ω : H}
                (f : singleton_h_valued_set X ω)
                (x₁ x₂ : X)
      : (h_valued_set_to_sheaf_mor_rel f x₁ ∧ h_valued_set_to_sheaf_mor_rel f x₂)
        ≤
        (x₁ ~_{X} x₂).
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      refine (cha_le_trans _ (singleton_h_valued_set_unique f _ _)).
      use cha_min_le_case.
      - refine (cha_le_trans (cha_min_le_l _ _) _).
        apply cha_min_le_r.
      - refine (cha_le_trans (cha_min_le_r _ _) _).
        apply cha_min_le_r.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_im
                {ω : H}
                (f : singleton_h_valued_set X ω)
      : cha_sheaf_rel (F := h_valued_set_to_sheaf) f f
        ≤
        \/_{ x : X } h_valued_set_to_sheaf_mor_rel f x.
    Proof.
      refine (cha_le_trans _ _).
      {
        use cha_eq_to_refl.
        exact (!(cha_sheaf_rel_partial_refl (F := h_valued_set_to_sheaf) f)).
      }
      refine (cha_le_trans _ _).
      {
        use cha_eq_to_refl.
        exact (!(cha_min_le_eq_l (singleton_h_valued_set_extent f))).
      }
      rewrite cha_frobenius.
      unfold h_valued_set_to_sheaf_mor_rel.
      apply cha_le_refl.
    Qed.

    Definition h_valued_set_to_sheaf_mor
      : h_valued_morphism
          H
          (sheaf_to_h_valued_set_functor _ h_valued_set_to_sheaf)
          X.
    Proof.
      use make_h_valued_morphism.
      - exact (λ ωf x, h_valued_set_to_sheaf_mor_rel (pr2 ωf) x).
      - intros ωf x.
        apply h_valued_set_to_sheaf_mor_rel_dom.
      - intros ωf x.
        apply h_valued_set_to_sheaf_mor_rel_cod.
      - intros ωf₁ ωf₂ x₁ x₂.
        apply h_valued_set_to_sheaf_mor_eq.
      - intros ωf x₁ x₂.
        apply h_valued_set_to_sheaf_mor_unique.
      - intro ωf.
        apply h_valued_set_to_sheaf_mor_im.
    Defined.

    Proposition h_valued_set_to_sheaf_mor_surjective
                (x : X)
      : (x ~_{X} x) ≤ \/_{ f } h_valued_set_to_sheaf_mor f x.
    Proof.
      use cha_le_lub.
      - refine ((x ~_{X} x) ,, _).
        exact (el_to_singleton_h_valued x).
      - cbn.
        unfold h_valued_set_to_sheaf_mor_rel.
        cbn.
        rewrite cha_min_id.
        apply cha_le_refl.
    Qed.

    Proposition h_valued_set_to_sheaf_mor_injective
                {ω₁ ω₂ : H}
                (f₁ : singleton_h_valued_set X ω₁)
                (f₂ : singleton_h_valued_set X ω₂)
                (x : X)
      : (h_valued_set_to_sheaf_mor_rel f₁ x ∧ h_valued_set_to_sheaf_mor_rel f₂ x)
        ≤
        cha_sheaf_rel (F := h_valued_set_to_sheaf) f₁ f₂.
    Proof.
      unfold h_valued_set_to_sheaf_mor_rel.
      use cha_le_lub.
      - simple refine (((ω₁ ∧ f₁ x) ∧ ω₂ ∧ f₂ x) ,, _ ,, _ ,, _).
        + refine (cha_le_trans (cha_min_le_l _ _) _).
          apply cha_min_le_l.
        + refine (cha_le_trans (cha_min_le_r _ _) _).
          apply cha_min_le_l.
        + cbn.
          use eq_singleton_h_valued_set.
          intro y.
          cbn.
          use cha_le_antisymm ; repeat use cha_min_le_case.
          * refine (cha_le_trans _ (singleton_h_valued_set_on_eq f₂ x y)).
            use cha_min_le_case.
            ** refine (cha_le_trans (cha_min_le_r _ _) _).
               refine (cha_le_trans (cha_min_le_r _ _) _).
               apply cha_min_le_r.
            ** refine (cha_le_trans _ (singleton_h_valued_set_unique f₁ x y)).
               use cha_min_le_case.
               *** refine (cha_le_trans (cha_min_le_r _ _) _).
                   refine (cha_le_trans (cha_min_le_l _ _) _).
                   apply cha_min_le_r.
               *** apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_min_le_r.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_r _ _) _).
            apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_r _ _) _).
            apply cha_min_le_r.
          * refine (cha_le_trans _ (singleton_h_valued_set_on_eq f₁ x y)).
            use cha_min_le_case.
            ** refine (cha_le_trans (cha_min_le_r _ _) _).
               refine (cha_le_trans (cha_min_le_l _ _) _).
               apply cha_min_le_r.
            ** refine (cha_le_trans _ (singleton_h_valued_set_unique f₂ x y)).
               use cha_min_le_case.
               *** refine (cha_le_trans (cha_min_le_r _ _) _).
                   refine (cha_le_trans (cha_min_le_r _ _) _).
                   apply cha_min_le_r.
               *** apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_l _ _) _).
            apply cha_min_le_r.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_r _ _) _).
            apply cha_min_le_l.
          * refine (cha_le_trans (cha_min_le_r _ _) _).
            refine (cha_le_trans (cha_min_le_r _ _) _).
            apply cha_min_le_r.
      - cbn.
        apply cha_le_refl.
    Qed.
  End HValuedSetToSheaf.

  (** * 4. Split essential surjectivity and the adjoint equivalence *)
  Definition split_eso_sheaf_to_h_valued_set_functor
    : split_essentially_surjective (sheaf_to_h_valued_set_functor H).
  Proof.
    refine (λ (X : h_valued_set H), _).
    refine (h_valued_set_to_sheaf X ,, _).
    use make_h_valued_isomorphism.
    - exact (h_valued_set_to_sheaf_mor X).
    - exact (h_valued_set_to_sheaf_mor_surjective X).
    - intros.
      apply h_valued_set_to_sheaf_mor_injective.
  Defined.

  Definition adj_equivalence_of_cats_sheaf_to_h_valued_set_functor
    : adj_equivalence_of_cats (sheaf_to_h_valued_set_functor H).
  Proof.
    use rad_equivalence_of_cats'.
    - exact fully_faithful_sheaf_to_h_valued_set_functor.
    - exact split_eso_sheaf_to_h_valued_set_functor.
  Defined.
End SheafToHValuedSetEso.

Arguments adj_equivalence_of_cats_sheaf_to_h_valued_set_functor : clear implicits.

Definition sheaves_h_valued_set_adj_equiv
           (H : complete_heyting_algebra)
  : adj_equiv
      (cat_of_sheaves (cha_to_site H))
      (topos_of_h_valued_sets H)
  := _ ,, adj_equivalence_of_cats_sheaf_to_h_valued_set_functor H.
