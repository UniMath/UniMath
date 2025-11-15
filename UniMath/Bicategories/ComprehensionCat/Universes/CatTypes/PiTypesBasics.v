(**

 Codes for ∏-types in a universe of a category

 A universe is said to be closed under ∏-types if the dependent product of any two types in
 that universe also is in that universe. In this file, we develop the basic theory of universes
 that are closed under ∏-types. Specifically, we define when a universe in a locally Cartesian
 closed category is closed under ∏-types, and we define when such functors preserve such codes.

 The ideas in this file are the same as for other type formers with the only difference being
 that we look at ∏-types. We require there to be an operation that assigns to every suitable
 pair of codes a new code representing their ∏-type. We work up to isomorphism, so the type
 associated to the code for the ∏-type is isomorphic  to their actual ∏-type. Finally, we also
 require that these codes are stable under substitution.

 The development on universes in locally Cartesian closed categories is split into two files.
 This is so that the files are shorter. The file (`PiTypes.v`) exports both files.

 Contents
 1. Codes for ∏-types
 2. Stability
 3. Preservation
 4. Preservation by identity
 5. Univalence condition

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section PiInCatWithUniv.
  Context {C : univ_cat_with_finlim_universe}
          {HC : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim C)}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  (** * 1. Codes for ∏-types *)
  Definition cat_univ_codes_pi
    : UU
    := ∏ (Γ : C)
         (a : Γ --> univ_cat_universe C)
         (b : cat_el_map_el el a --> univ_cat_universe C),
       ∑ (t : Γ --> univ_cat_universe C),
       z_iso
         (cat_el_map_slice el t)
         (lccc_exp_fib HC (cat_el_map_slice el a) (cat_el_map_slice el b)).

  Proposition isaset_cat_univ_codes_pi
    : isaset cat_univ_codes_pi.
  Proof.
    use impred_isaset ; intros Γ.
    use impred_isaset ; intros a.
    use impred_isaset ; intros b.
    use isaset_total2.
    - apply homset_property.
    - intros s.
      apply isaset_z_iso.
  Qed.

  Definition make_cat_univ_codes_pi
             (t : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (b : cat_el_map_el el a --> univ_cat_universe C),
                  Γ --> univ_cat_universe C)
             (f : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (b : cat_el_map_el el a --> univ_cat_universe C),
                  z_iso
                    (cat_el_map_slice el (t Γ a b))
                    (lccc_exp_fib HC (cat_el_map_slice el a) (cat_el_map_slice el b)))
    : cat_univ_codes_pi
    := λ Γ a b, t Γ a b ,, f Γ a b.

  Definition cat_univ_codes_pi_ty
             (Π : cat_univ_codes_pi)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
             (b : cat_el_map_el el a --> univ_cat_universe C)
    : Γ --> univ_cat_universe C
    := pr1 (Π Γ a b).

  Definition cat_univ_codes_pi_iso_slice
             (Π : cat_univ_codes_pi)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
             (b : cat_el_map_el el a --> univ_cat_universe C)
    : z_iso
        (cat_el_map_slice el (cat_univ_codes_pi_ty Π a b))
        (lccc_exp_fib HC (cat_el_map_slice el a) (cat_el_map_slice el b))
    := pr2 (Π Γ a b).

  Definition cat_univ_codes_pi_iso
             (Π : cat_univ_codes_pi)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
             (b : cat_el_map_el el a --> univ_cat_universe C)
    : cat_el_map_el el (cat_univ_codes_pi_ty Π a b)
      -->
      lccc_exp HC (cat_el_map_slice el a) (cat_el_map_slice el b)
    := dom_mor (z_iso_mor (cat_univ_codes_pi_iso_slice Π a b)).

  Proposition cat_univ_codes_pi_eq
              {Π₁ Π₂ : cat_univ_codes_pi}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_univ_codes_pi_ty Π₁ a b
                   =
                   cat_univ_codes_pi_ty Π₂ a b)
              (q : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_el_map_el_eq el (!(p Γ a b))
                   · cat_univ_codes_pi_iso Π₁ a b
                   =
                   cat_univ_codes_pi_iso Π₂ a b)
    : Π₁ = Π₂.
  Proof.
    use funextsec ; intro Γ.
    use funextsec ; intro a.
    use funextsec ; intro b.
    use total2_paths_f.
    - exact (p Γ a b).
    - use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : cat_el_map_slice el x --> _), is_z_isomorphism _)).
      }
      use eq_mor_cod_fib.
      unfold dom_mor.
      simpl.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : cat_el_map_el el x --> _), _)).
      }
      rewrite transportf_cat_el_map_el.
      exact (q Γ a b).
  Qed.

  Proposition cat_univ_codes_pi_ty_eq
              (Π : cat_univ_codes_pi)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a' --> univ_cat_universe C}
              (q : b = cat_el_map_el_eq el p · b')
    : cat_univ_codes_pi_ty Π a b
      =
      cat_univ_codes_pi_ty Π a' b'.
  Proof.
    induction p.
    cbn in q.
    rewrite id_left in q.
    induction q.
    apply idpath.
  Qed.

  Definition cat_univ_codes_pi_z_iso_eq_functor_mor
             (Π : cat_univ_codes_pi)
             {Γ : C}
             {a a' : Γ --> univ_cat_universe C}
             (p : a = a')
             {b : cat_el_map_el el a --> univ_cat_universe C}
             {b' : cat_el_map_el el a' --> univ_cat_universe C}
             (q : b = cat_el_map_el_eq el p · b')
    : cod_pb
        (pullbacks_univ_cat_with_finlim C)
        (cat_el_map_el_eq el (!p))
        (make_cod_fib_ob (cat_el_map_mor el b))
      -->
      make_cod_fib_ob (cat_el_map_mor el b').
  Proof.
    use make_cod_fib_mor.
    - exact (PullbackPr1 _ · cat_el_map_el_eq el q · cat_el_map_pb_mor _ _ _).
    - abstract
        (simpl ;
         rewrite !assoc' ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (cat_el_map_pb_mor_comm el (cat_el_map_el_eq el p) b')
         | ] ;
         etrans ;
         [ apply maponpaths ;
           rewrite assoc ;
           apply maponpaths_2 ;
           exact (cat_el_map_mor_eq el q)
         | ] ;
         rewrite !assoc ;
         rewrite PullbackSqrCommutes ;
         rewrite !assoc' ;
         rewrite (cat_el_map_el_eq_comp el) ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (cat_el_map_el_eq_id el)).
  Defined.

  Definition cat_univ_codes_pi_z_iso_eq_functor
             (Π : cat_univ_codes_pi)
             {Γ : C}
             {a a' : Γ --> univ_cat_universe C}
             (p : a = a')
             {b : cat_el_map_el el a --> univ_cat_universe C}
             {b' : cat_el_map_el el a' --> univ_cat_universe C}
             (q : b = cat_el_map_el_eq el p · b')
    : lccc_exp HC (cat_el_map_slice el a) (cat_el_map_slice el b)
      -->
      lccc_exp HC (cat_el_map_slice el a') (cat_el_map_slice el b').
  Proof.
    use lccc_exp_functor.
    - exact (cat_el_map_el_eq el (!p)).
    - abstract
        (exact (!(cat_el_map_mor_eq el (!p)))).
    - exact (cat_univ_codes_pi_z_iso_eq_functor_mor Π p q).
  Defined.

  Proposition cat_univ_codes_pi_z_iso_eq_lem
              (Π : cat_univ_codes_pi)
              {Γ : C}
              {a : Γ --> univ_cat_universe C}
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a --> univ_cat_universe C}
              (q : b = b')
              (r : cat_univ_codes_pi_ty Π a b = cat_univ_codes_pi_ty Π a b')
    : cat_el_map_el_eq el r
      · cat_univ_codes_pi_iso Π a b'
      =
      cat_univ_codes_pi_iso Π a b
      · cat_univ_codes_pi_z_iso_eq_functor Π (idpath _) (q @ !(id_left _)).
  Proof.
    induction q.
    assert (r = idpath _) as ->.
    {
      apply homset_property.
    }
    cbn.
    refine (id_left _ @ !(id_right _) @ !_).
    apply maponpaths.
    use lccc_exp_functor_on_id.
    - apply idpath.
    - cbn.
      etrans.
      {
        apply maponpaths.
        apply (cat_el_map_pb_mor_id el).
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (cat_el_map_el_eq_comp el _ _ @ _).
        apply cat_el_map_el_eq_id.
      }
      apply id_right.
  Qed.

  Proposition cat_univ_codes_pi_z_iso_eq
              (Π : cat_univ_codes_pi)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a' --> univ_cat_universe C}
              (q : b = cat_el_map_el_eq el p · b')
    : cat_el_map_el_eq el (cat_univ_codes_pi_ty_eq Π p q)
      · cat_univ_codes_pi_iso Π a' b'
      =
      cat_univ_codes_pi_iso Π a b
      · cat_univ_codes_pi_z_iso_eq_functor Π p q.
  Proof.
    induction p.
    etrans.
    {
      use cat_univ_codes_pi_z_iso_eq_lem.
      refine (q @ id_left _).
    }
    do 2 apply maponpaths.
    apply homset_property.
  Qed.

  Proposition cat_univ_codes_pi_z_iso_eq'
              (Π : cat_univ_codes_pi)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a' --> univ_cat_universe C}
              (q : b = cat_el_map_el_eq el p · b')
    : cat_el_map_el_eq el (!(cat_univ_codes_pi_ty_eq Π p q))
      · cat_univ_codes_pi_iso Π a b
      · cat_univ_codes_pi_z_iso_eq_functor Π p q
      =
      cat_univ_codes_pi_iso Π a' b'.
  Proof.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply cat_univ_codes_pi_z_iso_eq.
    }
    rewrite !assoc.
    rewrite cat_el_map_el_eq_comp.
    etrans.
    {
      apply maponpaths_2.
      apply cat_el_map_el_eq_id.
    }
    apply id_left.
  Qed.

  (** * 2. Stability *)
  Definition is_stable_cat_univ_codes_pi_functor
             {Γ Δ : C}
             (s : Γ --> Δ)
             (a : Δ --> univ_cat_universe C)
             (b : cat_el_map_el el a --> univ_cat_universe C)
    : lccc_exp
        HC
        (cat_el_map_slice el (s · a))
        (cat_el_map_slice el (cat_el_map_pb_mor el s a · b))
      -->
      cod_dom
        (lccc_exp_fib
           HC
           (cod_pb
              (pullbacks_univ_cat_with_finlim C)
              s (cat_el_map_slice el a))
           (cod_pb
              (pullbacks_univ_cat_with_finlim C)
              (PullbackPr1 _) (cat_el_map_slice el b))).
  Proof.
    use lccc_exp_functor.
    - exact (pb_mor_to_cat_stable_el_map_pb el s a).
    - abstract
        (refine (!_) ;
         apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el s a))).
    - use make_cod_fib_mor.
      + use PullbackArrow.
        * exact (PullbackPr1 _ · cat_el_map_pb_mor el _ _).
        * exact (PullbackPr2 _).
        * abstract
            (rewrite assoc' ;
             etrans ;
             [ apply maponpaths ;
               apply (PullbackSqrCommutes (cat_stable_el_map_pb _ _ _))
             | ] ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths_2 ;
               apply PullbackSqrCommutes
             | ] ;
             rewrite !assoc' ;
             apply maponpaths ;
             apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb _ _ _))).
      + abstract
          (apply PullbackArrow_PullbackPr2).
  Defined.

  Definition is_stable_cat_univ_codes_pi
             (Π : cat_univ_codes_pi)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : Δ --> univ_cat_universe C)
         (b : cat_el_map_el el a --> univ_cat_universe C),
       ∑ (p : s · cat_univ_codes_pi_ty Π a b
              =
              cat_univ_codes_pi_ty Π (s · a) (cat_el_map_pb_mor el s a · b)),
       dom_mor (#(cod_pb _ s) (cat_univ_codes_pi_iso_slice Π a b))
       · dom_mor (lccc_exp_fib_subst HC s (cat_el_map_slice el a) (cat_el_map_slice el b))
       =
       pb_mor_to_cat_stable_el_map_pb el s _
       · cat_el_map_el_eq el p
       · cat_univ_codes_pi_iso Π (s · a) (cat_el_map_pb_mor el s a · b)
       · is_stable_cat_univ_codes_pi_functor s a b.

  Proposition isaprop_is_stable_cat_univ_codes_pi
              (Π : cat_univ_codes_pi)
    : isaprop (is_stable_cat_univ_codes_pi Π).
  Proof.
    repeat (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_pi
    : UU
    := ∑ (Π : cat_univ_codes_pi),
       is_stable_cat_univ_codes_pi Π.

  Proposition isaset_cat_univ_stable_codes_pi
    : isaset cat_univ_stable_codes_pi.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_pi.
    - intro.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_codes_pi.
  Qed.

  Definition make_cat_univ_stable_codes_pi
             (Π : cat_univ_codes_pi)
             (H : is_stable_cat_univ_codes_pi Π)
    : cat_univ_stable_codes_pi
    := Π ,, H.

  Coercion cat_univ_stable_codes_pi_to_codes
           (Π : cat_univ_stable_codes_pi)
    : cat_univ_codes_pi
    := pr1 Π.

  Proposition cat_univ_stable_codes_pi_stable
              (Π : cat_univ_stable_codes_pi)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
              (b : cat_el_map_el el a --> univ_cat_universe C)
    : s · cat_univ_codes_pi_ty Π a b
      =
      cat_univ_codes_pi_ty Π (s · a) (cat_el_map_pb_mor el s a · b).
  Proof.
    exact (pr1 (pr2 Π Γ Δ s a b)).
  Defined.

  Proposition cat_univ_stable_codes_pi_z_iso_stable
              (Π : cat_univ_stable_codes_pi)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
              (b : cat_el_map_el el a --> univ_cat_universe C)
    : dom_mor (#(cod_pb _ s) (cat_univ_codes_pi_iso_slice Π a b))
     · dom_mor (lccc_exp_fib_subst HC s (cat_el_map_slice el a) (cat_el_map_slice el b))
      =
      pb_mor_to_cat_stable_el_map_pb el s _
      · cat_el_map_el_eq el (cat_univ_stable_codes_pi_stable Π s a b)
      · cat_univ_codes_pi_iso Π (s · a) (cat_el_map_pb_mor el s a · b)
      · is_stable_cat_univ_codes_pi_functor s a b.
  Proof.
    exact (pr2 (pr2 Π Γ Δ s a b)).
  Defined.

  Proposition cat_univ_stable_codes_pi_eq
              {Π₁ Π₂ : cat_univ_stable_codes_pi}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_univ_codes_pi_ty Π₁ a b
                   =
                   cat_univ_codes_pi_ty Π₂ a b)
              (q : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_el_map_el_eq el (!(p Γ a b))
                   · cat_univ_codes_pi_iso Π₁ a b
                   =
                   cat_univ_codes_pi_iso Π₂ a b)
    : Π₁ = Π₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_codes_pi.
    }
    use cat_univ_codes_pi_eq.
    - exact p.
    - exact q.
  Qed.
End PiInCatWithUniv.

Arguments cat_univ_codes_pi {C} HC.
Arguments cat_univ_stable_codes_pi {C} HC.

Section PreservationPiCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          {HC₁ : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim C₁)}
          {HC₂ : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim C₂)}
          (Π₁ : cat_univ_stable_codes_pi HC₁)
          (Π₂ : cat_univ_stable_codes_pi HC₂)
          {F : functor_finlim_universe C₁ C₂}
          (HF : preserves_locally_cartesian_closed
                  (functor_finlim_preserves_pullback F)
                  HC₁
                  HC₂).

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation *)
  Definition functor_preserves_stable_codes_pi_ty
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁)
         (b : cat_el_map_el el₁ a --> univ_cat_universe C₁),
       #F (cat_univ_codes_pi_ty Π₁ a b) · functor_on_universe F
       =
       cat_univ_codes_pi_ty
         Π₂
         (#F a · functor_on_universe F)
         (inv_from_z_iso (functor_el_map_iso Fel a)
          · #F b
          · functor_on_universe F).

  Definition functor_preserves_stable_codes_pi_z_iso_functor_mor
             {Γ : C₁}
             (a : Γ --> univ_cat_universe C₁)
             (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : cod_dom
        (cod_pb
           (pullbacks_univ_cat_with_finlim C₂)
           (functor_el_map_iso Fel a)
           (cat_el_map_slice
              el₂
              (inv_from_z_iso (functor_el_map_iso Fel a)
               · #F b
               · functor_on_universe F)))
      -->
      cod_dom (functor_on_cod_fib F (cat_el_map_slice el₁ b)).
  Proof.
    refine (PullbackPr1 _ · _).
    refine (_ · inv_from_z_iso (functor_el_map_iso Fel _)).
    refine (cat_el_map_el_eq el₂ (assoc' _ _ _) · _).
    apply cat_el_map_pb_mor.
  Defined.

  Proposition functor_preserves_stable_codes_pi_z_iso_functor_eq
             {Γ : C₁}
             (a : Γ --> univ_cat_universe C₁)
             (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : functor_preserves_stable_codes_pi_z_iso_functor_mor a b · cod_mor _
      =
      cod_mor _.
  Proof.
    unfold functor_preserves_stable_codes_pi_z_iso_functor_mor.
    simpl.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      do 2 apply maponpaths.
      exact (functor_el_map_comm Fel b).
    }
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      exact (PullbackSqrCommutes
               (cat_stable_el_map_pb
                  _
                  (inv_from_z_iso (functor_el_map_iso Fel a))
                  _)).
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply (cat_el_map_mor_eq el₂).
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply PullbackSqrCommutes.
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply z_iso_inv_after_z_iso.
    }
    apply id_right.
  Qed.

  Definition functor_preserves_stable_codes_pi_z_iso_functor_slice
             {Γ : C₁}
             (a : Γ --> univ_cat_universe C₁)
             (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : cod_pb
        (pullbacks_univ_cat_with_finlim C₂)
        (functor_el_map_iso Fel a)
        (cat_el_map_slice
           el₂
           (inv_from_z_iso (functor_el_map_iso Fel a)
            · #F b
            · functor_on_universe F))
      -->
      functor_on_cod_fib F (cat_el_map_slice el₁ b).
  Proof.
    use make_cod_fib_mor.
    - exact (functor_preserves_stable_codes_pi_z_iso_functor_mor a b).
    - exact (functor_preserves_stable_codes_pi_z_iso_functor_eq a b).
  Defined.

  Definition functor_preserves_stable_codes_pi_z_iso_functor
             {Γ : C₁}
             (a : Γ --> univ_cat_universe C₁)
             (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : lccc_exp
        HC₂
        (cat_el_map_slice el₂ (#F a · functor_on_universe F))
        (cat_el_map_slice
           el₂
           (inv_from_z_iso (functor_el_map_iso Fel a) · # F b · functor_on_universe F))
      -->
      lccc_exp
        HC₂
        (functor_on_cod_fib F (cat_el_map_slice el₁ a))
        (functor_on_cod_fib F (cat_el_map_slice el₁ b)).
  Proof.
    use lccc_exp_functor.
    - exact (functor_el_map_iso Fel _).
    - exact (functor_el_map_comm Fel _).
    - exact (functor_preserves_stable_codes_pi_z_iso_functor_slice a b).
  Defined.

  Definition functor_preserves_stable_codes_pi_z_iso
             (p : functor_preserves_stable_codes_pi_ty)
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁)
         (b : cat_el_map_el el₁ a --> univ_cat_universe C₁),
       #F(cat_univ_codes_pi_iso Π₁ a b)
       · preserves_locally_cartesian_closed_z_iso HF _ _
       =
       functor_el_map_iso Fel _
       · cat_el_map_el_eq el₂ (p Γ a b)
       · cat_univ_codes_pi_iso
           Π₂
           (#F a · functor_on_universe F)
           (inv_from_z_iso (functor_el_map_iso Fel a)
            · #F b
            · functor_on_universe F)
       · functor_preserves_stable_codes_pi_z_iso_functor a b.

  Definition functor_preserves_stable_codes_pi
    : UU
    := ∑ (p : functor_preserves_stable_codes_pi_ty),
       functor_preserves_stable_codes_pi_z_iso p.

  Proposition isaprop_functor_preserves_stable_codes_pi
    : isaprop functor_preserves_stable_codes_pi.
  Proof.
    use isaproptotal2.
    - intro.
      repeat (use impred ; intro).
      apply homset_property.
    - intros.
      repeat (use funextsec ; intro).
      apply homset_property.
  Qed.

  Definition make_functor_preserves_stable_codes_pi
             (p : functor_preserves_stable_codes_pi_ty)
             (q : functor_preserves_stable_codes_pi_z_iso p)
    : functor_preserves_stable_codes_pi
    := p ,, q.

  Proposition functor_preserves_stable_codes_pi_on_code
              (p : functor_preserves_stable_codes_pi)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
              (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : #F (cat_univ_codes_pi_ty Π₁ a b)
      · functor_on_universe F
      =
      cat_univ_codes_pi_ty
        Π₂
        (#F a · functor_on_universe F)
        (inv_from_z_iso (functor_el_map_iso Fel a)
         · #F b
         · functor_on_universe F).
  Proof.
    exact (pr1 p Γ a b).
  Defined.

  Proposition functor_preserves_stable_codes_pi_on_z_iso
              (p : functor_preserves_stable_codes_pi)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
              (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : #F(cat_univ_codes_pi_iso Π₁ a b)
      · preserves_locally_cartesian_closed_z_iso HF _ _
      =
      functor_el_map_iso Fel _
      · cat_el_map_el_eq el₂ (functor_preserves_stable_codes_pi_on_code p a b)
      · cat_univ_codes_pi_iso
          Π₂
          (#F a · functor_on_universe F)
          (inv_from_z_iso (functor_el_map_iso Fel a)
           · #F b
           · functor_on_universe F)
      · functor_preserves_stable_codes_pi_z_iso_functor a b.
  Proof.
    exact (pr2 p Γ a b).
  Defined.

  Proposition functor_preserves_stable_codes_pi_on_z_iso'
              (p : functor_preserves_stable_codes_pi)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
              (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : #F(cat_univ_codes_pi_iso Π₁ a b)
      =
      functor_el_map_iso Fel _
      · cat_el_map_el_eq el₂ (functor_preserves_stable_codes_pi_on_code p a b)
      · cat_univ_codes_pi_iso
          Π₂
          (#F a · functor_on_universe F)
          (inv_from_z_iso (functor_el_map_iso Fel a)
           · #F b
           · functor_on_universe F)
      · functor_preserves_stable_codes_pi_z_iso_functor a b
      · inv_from_z_iso (preserves_locally_cartesian_closed_z_iso HF _ _).
  Proof.
    rewrite <- functor_preserves_stable_codes_pi_on_z_iso.
    rewrite !assoc'.
    rewrite z_iso_inv_after_z_iso.
    rewrite id_right.
    apply idpath.
  Qed.
End PreservationPiCodes.

Arguments functor_preserves_stable_codes_pi
  {C₁ C₂ HC₁ HC₂} Π₁ Π₂ F.
Arguments functor_preserves_stable_codes_pi_ty
  {C₁ C₂ HC₁ HC₂} Π₁ Π₂ F.
Arguments functor_preserves_stable_codes_pi_z_iso
  {C₁ C₂ HC₁ HC₂ Π₁ Π₂} F HF p.
Arguments functor_preserves_stable_codes_pi_z_iso_functor
  {C₁ C₂ HC₂} F {Γ} a b.
Arguments functor_preserves_stable_codes_pi_on_code
  {C₁ C₂ HC₁ HC₂ Π₁ Π₂ F HF} p {Γ} a b.
Arguments functor_preserves_stable_codes_pi_on_z_iso
  {C₁ C₂ HC₁ HC₂ Π₁ Π₂ F HF} p {Γ} a b.
Arguments functor_preserves_stable_codes_pi_on_z_iso'
  {C₁ C₂ HC₁ HC₂ Π₁ Π₂ F HF} p {Γ} a b.

(** * 4. Preservation by identity and composition *)
Proposition identity_preserves_stable_codes_pi_ty
            {C : univ_cat_with_finlim_universe}
            {HC : is_locally_cartesian_closed
                     (pullbacks_univ_cat_with_finlim C)}
            (Π : cat_univ_stable_codes_pi HC)
  : functor_preserves_stable_codes_pi_ty Π Π (identity _).
Proof.
  intros Γ a b ; cbn.
  refine (id_right _ @ _).
  use cat_univ_codes_pi_ty_eq.
  - rewrite id_right.
    apply idpath.
  - refine (!_).
    etrans.
    {
      apply maponpaths.
      apply id_right.
    }
    refine (assoc _ _ _ @ _).
    rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply cat_el_map_el_eq_id.
Qed.

#[local] Opaque right_beck_chevalley_nat_trans.
#[local] Opaque preserves_locally_cartesian_closed_z_iso.

Proposition identity_preserves_stable_codes_pi_z_iso
            {C : univ_cat_with_finlim_universe}
            {HC : is_locally_cartesian_closed
                     (pullbacks_univ_cat_with_finlim C)}
            (Π : cat_univ_stable_codes_pi HC)
  : functor_preserves_stable_codes_pi_z_iso
      (identity _)
      (id_preserves_locally_cartesian_closed HC)
      (identity_preserves_stable_codes_pi_ty Π).
Proof.
  intros Γ a b.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply preserves_locally_cartesian_closed_z_iso_id.
  }
  refine (id_right _ @ _).
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths_2.
    exact (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C) _ _).
  }
  refine (!_).
  etrans.
  {
    refine (!_).
    use cat_univ_codes_pi_z_iso_eq'.
    - exact (a · functor_on_universe (identity _)).
    - apply id_right.
    - exact (inv_from_z_iso
               (functor_el_map_iso
                  (functor_finlim_universe_preserves_el (id₁ C))
                  a)
             · b
             · functor_on_universe (identity _)).
    - apply id_right.
  }
  use maponpaths_compose.
  - apply maponpaths_2.
    apply cat_el_map_el_eq_eq.
  - use lccc_exp_functor_eq.
    + apply idpath.
    + refine (!_).
      etrans.
      {
        do 2 refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        apply maponpaths.
        apply id_right.
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C) _ _ @ _).
      apply cat_el_map_el_eq_eq.
Qed.

Proposition identity_preserves_stable_codes_pi
            {C : univ_cat_with_finlim_universe}
            {HC : is_locally_cartesian_closed
                     (pullbacks_univ_cat_with_finlim C)}
            (Π : cat_univ_stable_codes_pi HC)
  : functor_preserves_stable_codes_pi
      Π Π
      (identity _)
      (id_preserves_locally_cartesian_closed HC).
Proof.
  use make_functor_preserves_stable_codes_pi.
  - exact (identity_preserves_stable_codes_pi_ty Π).
  - exact (identity_preserves_stable_codes_pi_z_iso Π).
Qed.

(** * 5. Univalence condition *)
Proposition pi_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {HC : is_locally_cartesian_closed
                     (pullbacks_univ_cat_with_finlim C)}
            {Π₁ Π₂ : cat_univ_stable_codes_pi HC}
            (Fc : functor_preserves_stable_codes_pi
                    Π₁ Π₂
                    (identity _)
                    (id_preserves_locally_cartesian_closed HC))
  : Π₁ = Π₂.
Proof.
  use cat_univ_stable_codes_pi_eq.
  - intros Γ a b.
    pose (functor_preserves_stable_codes_pi_on_code Fc a b) as p.
    simpl in p.
    refine (!(id_right _) @ _).
    refine (p @ _).
    use cat_univ_codes_pi_ty_eq ; cbn.
    + apply id_right.
    + apply id_right.
  - intros Γ a b.
    pose (functor_preserves_stable_codes_pi_on_z_iso' Fc a b) as p.
    simpl in p ; simpl.
    etrans.
    {
      apply maponpaths.
      exact p.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      }
      apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      exact (cat_univ_codes_pi_z_iso_eq' _ (id_right _) (id_right _)).
    }
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    refine (_ @ assoc _ _ _).
    use maponpaths_compose.
    {
      apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C)).
    }
    apply maponpaths.
    use z_iso_inv_on_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply preserves_locally_cartesian_closed_z_iso_id.
    }
    refine (id_right _ @ _).
    use lccc_exp_functor_eq.
    + apply idpath.
    + refine (!_).
      etrans.
      {
        do 2 refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        apply maponpaths.
        apply id_right.
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C) _ _ @ _).
      apply cat_el_map_el_eq_eq.
Qed.
