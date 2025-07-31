(**

 Categories with universes versus comprehension categories with universes: the unit

 Our goal is to establish a biequivalence between the bicategories of univalent categories
 with finite limits and a universe type and the bicategory of univalent full DFL comprehension
 categories that have a universe. In this file, we construct the unit of this biadjunction.

 The mathematical development in this file is not the most exciting on the planet. Most of
 the calculations are rather straightforward. However, the lack of interesting aspects in
 the mathematical development is compensated: there are various points where trickery
 (basically dark magic) is necessary to guaranteed that the file compiles in an acceptable
 amount of time. These points are detailed in the file.

 Contents
 1. Action on objects
 1.1. Preservation of the object
 1.2. Preservation of the associated type
 1.3. The coherences
 2. Action on 1-cells
 2.1. Coherence for the object
 2.2. Coherence for the associated type
 3. The displayed pseudotransformation

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.FinLimToCompCatLemmas.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivCell.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivIdent.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Action on objects *)
Section UnitMor.
  Context {C : univ_cat_with_finlim_ob}
          (el : cat_stable_el_map_coherent C).

  Let u : C := univ_cat_universe C.
  Let CC : dfl_full_comp_cat := finlim_to_dfl_comp_cat_psfunctor (pr1 C).

  Let ηC : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim CC
       ,,
       dfl_full_comp_cat_to_finlim_ob (C := CC) (finlim_to_comp_cat_universe_ob C).

  Let η_el : cat_stable_el_map ηC
    := dfl_full_comp_cat_to_finlim_stable_el_map
         (C := CC)
         (finlim_to_comp_cat_universe_ob C)
         (finlim_to_comp_cat_univ_type el).

  (** * 1.1. Preservation of the object *)
  Definition finlim_dfl_comp_cat_unit_ob
    : functor_finlim_ob ηC C.
  Proof.
    refine (finlim_dfl_comp_cat_unit_mor C ,, _).
    apply identity_z_iso.
  Defined.

  Arguments finlim_dfl_comp_cat_unit_ob /.

  Proposition finlim_dfl_comp_cat_unit_ob_on_mor
              {x y : C}
              (f : x --> y)
    : #finlim_dfl_comp_cat_unit_ob f = f.
  Proof.
    apply idpath.
  Qed.

  (** * 1.2. Preservation of the associated type *)
  Proposition finlim_dfl_comp_cat_unit_el_map_ob_eq
              {Γ : C}
              (t : Γ --> univ_cat_universe C)
    : finlim_univ_tm_to_mor
        (dfl_full_comp_cat_mor_to_tm (C := CC) (finlim_to_comp_cat_universe_ob C) t)
      =
      t · identity _.
  Proof.
    unfold finlim_univ_tm_to_mor, dfl_full_comp_cat_mor_to_tm.
    cbn.
    refine (_ @ !(id_right _)).
    apply (PullbackArrow_PullbackPr1
             (comp_cat_pullback (finlim_to_comp_cat_universe_ob C) _)).
  Qed.

  Definition finlim_dfl_comp_cat_unit_el_map_ob
             {Γ : C}
             (t : Γ --> univ_cat_universe C)
    : z_iso
        (cat_el_map_el
           el
           (finlim_univ_tm_to_mor
              (dfl_full_comp_cat_mor_to_tm
                 (C := CC)
                 (finlim_to_comp_cat_universe_ob C)
                 t)))
        (cat_el_map_el el (t · id₁ _))
    := cat_el_map_el_eq el (finlim_dfl_comp_cat_unit_el_map_ob_eq t).

  Arguments finlim_dfl_comp_cat_unit_el_map_ob {Γ} t /.

  Definition finlim_dfl_comp_cat_unit_el_map
    : functor_el_map η_el el finlim_dfl_comp_cat_unit_ob.
  Proof.
    use make_functor_el_map.
    - exact (λ Γ t, finlim_dfl_comp_cat_unit_el_map_ob t).
    - abstract
        (intros Γ t ;
         unfold finlim_dfl_comp_cat_unit_el_map_ob ;
         refine (!_) ;
         apply (cat_el_map_mor_eq el)).
  Defined.

  (** * 1.3. The coherences *)

  (**
     The following lemma is factored out from [finlim_dfl_comp_cat_unit_stable_el_map].
     The type of the goal is written down explicitly, which enables a nice usage of
     tactics. If `cbn` is used in [finlim_dfl_comp_cat_unit_stable_el_map], then the
     type checking time of the final `Qed` takes too much time.
   *)
  Local Lemma finlim_dfl_comp_cat_unit_stable_el_map_lem
              {Γ Δ : ηC}
              (s : Γ --> Δ)
              (t : Δ --> univ_cat_universe ηC)
              p
              q
    : dfl_full_comp_cat_to_finlim_el_map_stable_mor
        (C := CC)
        (finlim_to_comp_cat_universe_ob C)
        (finlim_to_comp_cat_univ_type el)
        s t
      · cat_el_map_el_eq el p
      =
      cat_el_map_el_eq el q
      · cat_el_map_pb_mor el s (t · identity _).
  Proof.
    etrans.
    {
      unfold dfl_full_comp_cat_to_finlim_el_map_stable_mor.
      apply maponpaths_2.
      apply (comprehension_functor_mor_transportf
               (comp_cat_comprehension (finlim_to_dfl_comp_cat (pr1 C)))).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (univ_cat_with_finlim_comprehension_functor _).
    }
    simpl.
    do 2 refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply finlim_comp_cat_el_map_on_eq.
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      rewrite id_right.
      apply maponpaths.
      apply (PullbackArrow_PullbackPr1
               (comp_cat_pullback (finlim_to_comp_cat_universe_ob C) _)).
    }
    do 2 refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply cat_el_map_el_eq_inv.
    }
    etrans.
    {
      apply maponpaths_2.
      apply (cat_el_map_el_eq_comp el).
    }
    etrans.
    {
      apply (cat_el_map_el_eq_comp el).
    }
    apply (cat_el_map_el_eq_eq el).
  Qed.

  Proposition finlim_dfl_comp_cat_unit_stable_el_map
    : functor_stable_el_map finlim_dfl_comp_cat_unit_el_map.
  Proof.
    intros Γ Δ s t.
    refine (finlim_dfl_comp_cat_unit_stable_el_map_lem s t _ _ @ _).
    apply maponpaths_2.
    refine (!_).
    apply cat_el_map_el_eq_comp.
  Qed.

  Definition finlim_dfl_comp_cat_unit_preserves_el
    : functor_preserves_el
        η_el
        el
        finlim_dfl_comp_cat_unit_ob.
  Proof.
    use make_functor_preserves_el.
    - exact finlim_dfl_comp_cat_unit_el_map.
    - exact finlim_dfl_comp_cat_unit_stable_el_map.
  Defined.
End UnitMor.

(** * 2. Action on 1-cells *)

(**
   In this part, more trickery is needed to guarantee acceptable compilation times.
 *)
Section UnitNat.
  Context {C₁ C₂ : univ_cat_with_finlim_ob}
          {F : functor_finlim_ob C₁ C₂}
          {el₁ : cat_stable_el_map_coherent C₁}
          {el₂ : cat_stable_el_map_coherent C₂}
          (Fu : functor_preserves_el el₁ el₂ F).

  Let CC₁ : dfl_full_comp_cat := finlim_to_dfl_comp_cat_psfunctor (pr1 C₁).
  Let CC₂ : dfl_full_comp_cat := finlim_to_dfl_comp_cat_psfunctor (pr1 C₂).

  Let FC₁ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim (finlim_to_dfl_comp_cat_psfunctor (pr1 C₁))
       ,,
       dfl_full_comp_cat_to_finlim_ob (C := CC₁) (finlim_to_comp_cat_universe_ob C₁).
  Let FC₂ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim (finlim_to_dfl_comp_cat_psfunctor (pr1 C₂))
       ,,
       dfl_full_comp_cat_to_finlim_ob (C := CC₂) (finlim_to_comp_cat_universe_ob C₂).

  Let FF : functor_finlim_ob FC₁ FC₂
    := dfl_functor_comp_cat_to_finlim_functor (finlim_to_dfl_comp_cat_functor F)
       ,,
       dfl_full_comp_cat_functor_preserves_ob
         (finlim_to_dfl_comp_cat_functor F)
         (finlim_to_comp_cat_functor_ob_mor F).

  (** 2.1. Coherence for the object *)
  Proposition finlim_dfl_comp_cat_unit_natural_ob
    : nat_trans_finlim_ob
        (finlim_dfl_comp_cat_unit_ob · F)
        (FF · finlim_dfl_comp_cat_unit_ob).
  Proof.
    refine (finlim_dfl_comp_cat_unit_natural F ,, _).
    abstract
      (refine (id_left _ @ _) ;
       refine (id_right _ @ _) ;
       refine (id_left _ @ _) ;
       refine (!_) ;
       refine (maponpaths (λ z, z · _) (functor_id _ _) @ _) ;
       refine (id_left _ @ _) ;
       apply idpath).
  Defined.

  (** 2.2. Coherence for the associated type *)

  (**
     We add notation for [GG₁] and [GG₂] to have control over their types. This
     helps controlling the unifier and to reduce compilation times. For instance,
     if the type of [GG₁] is removed, then reading the statement of the lemma
     [finlim_dfl_comp_cat_unit_natural_el_lem_iso_GG] would take 8 seconds rather
     than 0.034 seconds. The reason why this helps, is because the extra type
     information means that the unifier has to compute less (and it is these
     computations that delay compilation time).
   *)
  Let GG₁
    : functor_preserves_el
        (dfl_full_comp_cat_to_finlim_stable_el_map
           (C := CC₁)
           (finlim_to_comp_cat_universe_ob C₁)
           (finlim_to_comp_cat_univ_type el₁))
        (dfl_full_comp_cat_to_finlim_stable_el_map
           (C := CC₂)
           (finlim_to_comp_cat_universe_ob C₂)
           (finlim_to_comp_cat_univ_type el₂))
        FF
    := dfl_full_comp_cat_functor_preserves_el
         (finlim_to_dfl_comp_cat_functor F)
         (finlim_to_comp_cat_functor_ob_mor F)
         (finlim_to_comp_cat_functor_preserves_univ_type Fu).

  Local Lemma comp_GG₁
              {Γ : FC₁}
              (t : Γ --> univ_cat_universe FC₁)
    : pr1 (functor_el_map_iso GG₁ t)
      =
      pr1 (dfl_full_comp_cat_functor_preserves_el_map_iso
             (finlim_to_dfl_comp_cat_functor F)
             (finlim_to_comp_cat_functor_ob_mor F)
             (finlim_to_comp_cat_functor_preserves_univ_type Fu)
             t).
  Proof.
    apply idpath.
  Qed.

  Opaque GG₁.

  Let GG₂
    : functor_preserves_el
        (dfl_full_comp_cat_to_finlim_stable_el_map
           (C := CC₂)
           (finlim_to_comp_cat_universe_ob C₂)
           (finlim_to_comp_cat_univ_type el₂))
        el₂
        finlim_dfl_comp_cat_unit_ob
    := finlim_dfl_comp_cat_unit_preserves_el el₂.

  Opaque GG₂.

  (**
     In the following lemma, we construct the inhabitant of a ∑-type, which might seem
     surprising at first. The reason for using this ∑-type is as follows. We do not want
     to write down an explicit expression for `p` in the type, because that would make
     the type more unreadable and convoluted. Instead we want to just prove the equality
     and not care about `p`, because in the end of the prove, this `p` is uniquely
     determined. To do this, we say that there is some `p` that satisfies this requirement,
     we start the proof with `eexists`, so that this `p` is represented by a metavariable.
     In the final step of the proof, the metavariable is instantiated. At this point, two
     terms must be equal, and `p` is a subterm of one of them.
   *)
  Local Lemma finlim_dfl_comp_cat_unit_natural_el_lem_iso_GG
              {Γ : FC₁}
              (t : Γ --> univ_cat_universe FC₁)
    : ∑ p,
      pr1 (functor_el_map_iso GG₁ t)
      =
      functor_el_map_iso
        Fu
        (finlim_univ_tm_to_mor
           (dfl_full_comp_cat_mor_to_tm
              (C := CC₁)
              (finlim_to_comp_cat_universe_ob C₁)
              t))
      · cat_el_map_el_eq el₂ p.
  Proof.
    eexists.
    simpl.
    etrans.
    {
      apply (comp_GG₁ t).
    }
    simpl.
    etrans.
    {
      apply maponpaths_2.
      exact (finlim_to_comprehension_nat_trans_mor
               F
               (comp_cat_univ_el
                  (finlim_to_comp_cat_univ_type el₁)
                  (dfl_full_comp_cat_mor_to_tm
                     (C := CC₁)
                     (finlim_to_comp_cat_universe_ob C₁)
                     t))).
    }
    etrans.
    {
      apply maponpaths.
      apply (comp_in_cod_fib
               (finlim_to_comp_cat_functor_preserves_el_mor
                  Fu
                  (dfl_full_comp_cat_mor_to_tm
                     (C := CC₁)
                     (finlim_to_comp_cat_universe_ob C₁)
                     t))).
    }
    simpl.
    rewrite assoc'.
    etrans.
    {
      do 3 apply maponpaths.
      exact (finlim_comp_cat_el_map_on_eq
               el₂
               (dfl_full_comp_cat_functor_preserves_el_map_eq
                  (finlim_to_dfl_comp_cat_functor F)
                  (finlim_to_comp_cat_functor_ob_mor F)
                  t)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply cat_el_map_el_eq_comp.
    }
    apply id_left.
  Qed.

  (**
     We use the same trick with the ∑-type, because it is useful for this lemma as well.
     Also for the following lemmas.
   *)
  Local Lemma finlim_dfl_comp_cat_unit_natural_el_lem
              {Γ : FC₁}
              (t : Γ --> univ_cat_universe FC₁)
    : ∑ p,
      identity _
      · functor_el_map_iso
          (comp_functor_preserves_el GG₁ GG₂)
          t
      =
      functor_el_map_iso Fu
        (finlim_univ_tm_to_mor
           (dfl_full_comp_cat_mor_to_tm
              (C := CC₁)
              (finlim_to_comp_cat_universe_ob C₁)
              t))
      · cat_el_map_el_eq el₂ p.
  Proof.
    eexists.
    refine (id_left _ @ _).
    refine (comp_functor_el_map_on_tm GG₁ GG₂ t @ _).
    rewrite assoc'.
    etrans.
    {
      apply maponpaths_2.
      apply finlim_dfl_comp_cat_unit_ob_on_mor.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (pr2 (finlim_dfl_comp_cat_unit_natural_el_lem_iso_GG t)).
    }
    rewrite assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply (cat_el_map_el_eq_comp el₂).
    }
    etrans.
    {
      apply maponpaths.
      apply (cat_el_map_el_eq_comp el₂).
    }
    (**
       We need to do `simpl` to make `apply idpath` run in acceptable time.
     *)
    simpl.
    apply idpath.
  Qed.

  Local Lemma functor_el_map_iso_finlim_dfl_comp_cat_unit_preserves_el
              {Γ : C₁}
              (t : Γ --> univ_cat_universe C₁)
    : ∑ p,
      pr1 (functor_el_map_iso
             (comp_functor_preserves_el
                (finlim_dfl_comp_cat_unit_preserves_el el₁)
                Fu)
             t)
      =
      functor_el_map_iso Fu
        (finlim_univ_tm_to_mor
           (dfl_full_comp_cat_mor_to_tm
              (C := CC₁)
              (finlim_to_comp_cat_universe_ob C₁)
              t))
      · cat_el_map_el_eq el₂ p.
  Proof.
    eexists.
    cbn.
    etrans.
    {
      apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq Fu).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      rewrite z_iso_after_z_iso_inv.
      apply id_left.
    }
    apply (cat_el_map_el_eq_comp el₂).
  Qed.

  Local Lemma functor_el_map_iso_finlim_dfl_comp_cat_unit_preserves_el_comp
              {Γ : C₁}
              (t : Γ --> univ_cat_universe C₁)
    : ∑ p,
      functor_el_map_iso
        (comp_functor_preserves_el (finlim_dfl_comp_cat_unit_preserves_el el₁) Fu)
        t
      · cat_el_map_el_eq el₂ (nat_trans_preserves_el_path _ _)
      · cat_el_map_pb_mor
          el₂
          (finlim_dfl_comp_cat_unit_natural_ob Γ)
          _
      =
      functor_el_map_iso
        (comp_functor_preserves_el
           (finlim_dfl_comp_cat_unit_preserves_el el₁)
           Fu)
        t
      · cat_el_map_el_eq el₂ p.
  Proof.
    eexists.
    etrans.
    {
      apply maponpaths.
      apply (cat_el_map_pb_mor_id el₂).
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_el_eq_comp.
    }
    apply idpath.
  Qed.

  Local Lemma finlim_dfl_comp_cat_unit_natural_el_lem_2
              {Γ : C₁}
              (t : Γ --> univ_cat_universe C₁)
              p
    : functor_el_map_iso
        (comp_functor_preserves_el
           (finlim_dfl_comp_cat_unit_preserves_el el₁)
           Fu)
        t
      · cat_el_map_el_eq
          el₂
          (pr1 (functor_el_map_iso_finlim_dfl_comp_cat_unit_preserves_el_comp t))
      =
      functor_el_map_iso Fu
        (finlim_univ_tm_to_mor
           (dfl_full_comp_cat_mor_to_tm
              (C := CC₁)
              (finlim_to_comp_cat_universe_ob C₁)
              t))
      · cat_el_map_el_eq el₂ p.
  Proof.
    (**
       Neither [functor_el_map_iso] nor [comp_functor_preserves_el] should be unfolded,
       because that would make the goal a little ugly and it would make the compilation
       time of the proof too much. The slowest line is the line where the lemma
       [functor_el_map_iso_finlim_dfl_comp_cat_unit_preserves_el] is used. Currently, it
       runs in 27 seconds, but if `cbn` were used instead, then the running time of that
       line would be 43 seconds.
     *)
    cbn -[functor_el_map_iso comp_functor_preserves_el].
    etrans.
    {
      apply maponpaths_2.
      refine (pr2 (functor_el_map_iso_finlim_dfl_comp_cat_unit_preserves_el t) @ _).
      cbn.
      apply idpath.
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply (cat_el_map_el_eq_comp el₂).
    }
    cbn.
    apply (cat_el_map_el_eq_eq el₂).
  Qed.

  Proposition finlim_dfl_comp_cat_unit_natural_el
    : nat_trans_preserves_el
        finlim_dfl_comp_cat_unit_natural_ob
        (comp_functor_preserves_el
           (finlim_dfl_comp_cat_unit_preserves_el el₁)
           Fu)
        (comp_functor_preserves_el
           (dfl_full_comp_cat_functor_preserves_el
              (finlim_to_dfl_comp_cat_functor F)
              _
              (finlim_to_comp_cat_functor_preserves_univ_type Fu))
           (finlim_dfl_comp_cat_unit_preserves_el el₂)).
  Proof.
    intros Γ t.
    refine (pr2 (finlim_dfl_comp_cat_unit_natural_el_lem t) @ _).
    refine (_ @ !(pr2 (functor_el_map_iso_finlim_dfl_comp_cat_unit_preserves_el_comp t))).
    exact (!(finlim_dfl_comp_cat_unit_natural_el_lem_2 t _)).
  Qed.
End UnitNat.

(** * 3. The displayed pseudotransformation *)
Definition dfl_comp_cat_to_finlim_disp_psfunctor_unit
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_to_dfl_comp_cat_disp_psfunctor_universe
         dfl_comp_cat_to_finlim_disp_psfunctor_universe)
      (disp_pseudo_id disp_bicat_finlim_universe)
      finlim_dfl_comp_cat_unit.
Proof.
  use make_disp_pstrans.
  - exact disp_2cells_isaprop_disp_bicat_finlim_universe.
  - exact disp_locally_groupoid_disp_bicat_finlim_universe.
  - intros C u.
    refine (_ ,, _).
    exact (finlim_dfl_comp_cat_unit_preserves_el (pr2 u)).
  - intros C₁ C₂ F u₁ u₂ Fu.
    refine (_ ,, _).
    exact (finlim_dfl_comp_cat_unit_natural_el (pr2 Fu)).
Defined.
