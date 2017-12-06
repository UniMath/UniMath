(**
- Definition of an effective epimorphism.
- Proof that natural transformations that are pointwise effective epis are
 effective epis.
- Proof that if the target category has pushouts, a natural transformation that is
  an epimorphism is pointwise epimorphic
- Faithul functors reflect epimorphisms
- Definition of a split epimorphism
- Split epis are absolute (ie are preserved by any functor)

Ambroise LAFONT January 2017
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Local Open Scope cat.

(** Definition of an effective epimorphism.
An effective epimorphism p: A -> B is a morphism which has a kernel pair and which
is the coequalizer of its kernel pair.
*)
Section EffectiveEpi.
  Context {C:precategory} {A B:C}.
  Variable (f: C ⟦A,B⟧).

  Definition kernel_pair := Pullback  f f.

  Definition isEffective :=
    ∑  g:kernel_pair,
         (isCoequalizer (PullbackPr1 g)
                        (PullbackPr2 g) f (PullbackSqrCommutes g)).
End EffectiveEpi.

Definition EpisAreEffective (C:precategory) :=
  ∏ (A B:C) (f:C⟦A,B⟧), isEpi f -> isEffective f.




(** Let f be a natural transformation. If f is pointwise effective, then f is effective *)
Section IsEffectivePw.

  Context {C : precategory} {D : category} .

  Local Notation CD := (functor_category C D).

  Lemma eq_pb_pw {X Y Z:functor C D}
        (a: X ⟹ Z) (b: Y ⟹ Z)
        (c:C)
    : eq_diag
        (pullback_diagram D (a c)  (b c))
        (diagram_pointwise (homset_property D)
                           (pullback_diagram CD a b) c).
  Proof.
    intros.
    use tpair.
    use StandardFiniteSets.three_rec_dep; apply idpath.
    use StandardFiniteSets.three_rec_dep;  use StandardFiniteSets.three_rec_dep;
      exact (Empty_set_rect _ ) ||  (exact (λ _, idpath _)).
  Defined.

  Lemma eq_coeq_pw {X Y: functor C D} (a b:X ⟹ Y) (c:C) :
    eq_diag
      (Coequalizer_diagram D (a c) (b c))
      (diagram_pointwise (homset_property D)
                         (Coequalizer_diagram CD a b) c).
  Proof.
    intros.
    use tpair.
    use StandardFiniteSets.two_rec_dep; reflexivity.
    use StandardFiniteSets.two_rec_dep;  use StandardFiniteSets.two_rec_dep;
       try exact (Empty_set_rect _ ).
    intros g'.
    destruct g'.
    apply idpath.
    apply idpath.
  Defined.

  Context {X Y :functor C D } {a:X ⟹ Y}.

  Lemma isEffectivePw : (∏ (x:C), isEffective (a x)) -> isEffective (C:=CD) a.
  Proof.
    intros h.
    red.
    transparent assert (f:(kernel_pair (C:=CD) a)).
    { apply equiv_Pullback_2;[apply homset_property|].
      apply LimFunctorCone.
      intro c.
      specialize (h c).
      set (f := pr1 h).
      apply equiv_Pullback_1 in f;[|apply homset_property].
      use (eq_diag_liftlimcone _  _  f).
      apply eq_pb_pw.
    }
    exists f.
    apply equiv_isCoequalizer2;[apply homset_property|].
    apply  pointwise_Colim_is_isColimFunctor.
    intro x.
    set (g:= f).
    assert (hf := (pr2 (h x))); simpl in hf.
    apply equiv_isCoequalizer1 in hf;[|apply homset_property].
    set (eqd := eq_coeq_pw (PullbackPr1 g) (PullbackPr2 g) x).
    set (z:= (eq_diag_iscolimcocone _ eqd hf)).
    set (CC := (mk_ColimCocone _ _ _ z)).
    apply (is_iso_isColim (homset_property D) _ CC).
    rewrite <- (colimArrowUnique CC _ _ (identity _)).
    apply identity_is_iso.
    use StandardFiniteSets.two_rec_dep;
    cbn beta;
    rewrite id_right;
    apply idpath.
  Qed.



End IsEffectivePw.

(**  if the target category has pushouts, a natural transformation that is
  an epimorphism is pointwise epimorphic *)
Section PointwiseEpi.

  Context {C : precategory} {D : category}.

  Local Notation CD := (functor_category C D).

  Lemma eq_po_pw {X Y Z :functor C D} {a: X ⟹ Y } {b: X ⟹ Z} x  :
    eq_diag
      (pushout_diagram D (a x) (b x))
      (diagram_pointwise (homset_property D)
                         (pushout_diagram CD a b) x).
  Proof.
    use tpair.
    use StandardFiniteSets.three_rec_dep;  apply idpath.
    use StandardFiniteSets.three_rec_dep;  use StandardFiniteSets.three_rec_dep;
      exact (Empty_set_rect _ )||exact (λ _, idpath _).
  Defined.

  Lemma Pushouts_pw_epi (colimD : graphs.pushouts.Pushouts D) (A B : functor C D)
       (a: A ⟹ B)  (epia:isEpi (C:=CD) a) : ∏ (x:C), isEpi (a x).
  Proof.
    intro  x; simpl.
    apply (epi_to_pushout (C:=CD)) in epia.
    apply pushout_to_epi.
    simpl.
    apply equiv_isPushout1 in epia; [| apply homset_property].
    apply equiv_isPushout2; [ apply homset_property|].
    red in epia.
    red.
    eapply (isColimFunctor_is_pointwise_Colim
              (homset_property _)) in epia; cycle 1.
    {
      intro c.
      eapply eq_diag_liftcolimcocone.
      - apply eq_po_pw.
      - apply colimD.
    }
    apply (eq_diag_iscolimcocone _ (sym_eq_diag _ _ (eq_po_pw x)))in epia; cycle 1.
    set (CC := (mk_ColimCocone _ _ _ epia)).
    eapply (is_iso_isColim (homset_property D) _ CC).
    rewrite <- (colimArrowUnique CC _ _ (identity _)).
    apply identity_is_iso.
    use StandardFiniteSets.three_rec_dep;
    cbn beta;
    rewrite id_right;
    apply idpath.
  Qed.

End PointwiseEpi.

(** faithul functors reflect epimorphisms *)
Lemma faithful_reflects_epis {C D:precategory} (U:functor C D) (hU:faithful U)
      {a b:C} (f:C⟦a,b⟧) : isEpi (#U f) -> isEpi f.
Proof.
  intros hf c u v huv.
  eapply invmaponpathsincl.
  apply hU.
  cbn.
  apply hf.
  rewrite <- functor_comp, <- functor_comp.
  now rewrite huv.
Qed.

(** Definition of a split epimorphism.
It is a morphism f such that there exists a morphism g that satisfies f ∘ g = id
*)
Section SplitEpis.

Section DefSplitEpis.

Context {C:precategory} {A B:C} (f:C⟦A,B⟧).
Definition isSplitEpi :=
  ∥ ∑  (g:C⟦B,A⟧), g · f = identity B ∥.


Lemma isSplitEpi_isEpi {hsc:has_homsets C} (split_f:isSplitEpi): isEpi f.
Proof.
  apply (squash_to_prop split_f).
  - now apply isapropisEpi.
  - intros hf z u v e.
    rewrite <- (id_left u), <- (id_left v).
    rewrite <- (pr2 hf).
    repeat rewrite <- assoc.
    now apply cancel_precomposition.
Qed.

End DefSplitEpis.

Definition EpisAreSplit (C:precategory) :=
  ∏ (A B:C) (f:C⟦A,B⟧), isEpi f -> isSplitEpi f.

(** Functors preserve split epimorphisms *)
Lemma preserves_isSplitEpi {C D:precategory} (F:functor C D)
      {A B : C} (f:C⟦A,B⟧) : isSplitEpi f -> isSplitEpi (#F f).
Proof.
  apply hinhfun.
  intro hf.
  exists (#F (pr1 hf)).
  now rewrite <-functor_id,<- (pr2 hf), <- functor_comp.
Qed.

End SplitEpis.
