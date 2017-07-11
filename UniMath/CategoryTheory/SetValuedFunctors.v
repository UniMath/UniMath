(**
Facts about set valued functors

- epimorphic natural transformations are pointwise epimorphic
- epimorphic natural transformations enjoy a universal property similar to
surjections [univ_surj_nt]
- Definition of a quotient functor

Ambroise LAFONT January 2017
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Local Open Scope cat.


Lemma is_pointwise_epi_from_set_nat_trans_epi (C:precategory)
      (F G : functor C hset_precategory) (f:nat_trans F G)
      (h:isEpi (C:=functor_precategory C _ has_homsets_HSET) f)
  : ∏ (x:C), isEpi (f x).
Proof.
  apply (Pushouts_pw_epi (D:=hset_category)).
  apply PushoutsHSET_from_Colims.
  apply h.
Qed.

(**
Let p be an epimorphic natural transformation where the target category is HSET

Given the following diagram :
<<<
    f
 A ---> C
 |
 | p
 |
 v
 B
>>>
there exists a unique natural transformation from B to C that makes the diagram
commute provided that for any set X, any x,y in X, if [p x = p y] then [f x = f y]

This property comes from the fact that p is an effective epimorphism.
*)
Section LiftEpiNatTrans.

  Context { CC:precategory}.
  Local Notation C_SET :=  (functor_precategory CC HSET has_homsets_HSET).


  Context {A B C:functor CC HSET} (p:nat_trans A B)
          (f:nat_trans A C).

  Hypothesis (comp_epi: ∏ (X:CC)  (x y: pr1hSet (A X)),
                        p X x =  p X y -> f X x = f X y).

  Hypothesis (surjectivep : isEpi (C:=C_SET) p).

  Lemma EffectiveEpis_Functor_HSET : EpisAreEffective C_SET.
  Proof.
    intros F G m isepim.
    apply (isEffectivePw (D:=hset_category)).
    intro x.
    apply EffectiveEpis_HSET.
    apply (Pushouts_pw_epi (D:=hset_category)
                           PushoutsHSET_from_Colims).
    assumption.
  Qed.

  Definition univ_surj_nt : nat_trans B C.
  Proof.
    apply EffectiveEpis_Functor_HSET in surjectivep.
    red in surjectivep.
    set (coeq := limits.coequalizers.mk_Coequalizer _ _ _ _ (pr2 surjectivep)).
    apply (limits.coequalizers.CoequalizerOut coeq _ f).
    abstract(
    apply (nat_trans_eq (has_homsets_HSET));
    intro c;
    apply funextfun;
    intro x;
    apply comp_epi;
    assert (hcommut := limits.pullbacks.PullbackSqrCommutes (pr1 surjectivep));
    eapply nat_trans_eq_pointwise in hcommut;
    apply toforallpaths in hcommut;
    apply hcommut).
  Defined.

  Lemma univ_surj_nt_ax : nat_trans_comp _ _ _ p univ_surj_nt = f .
  Proof.
    unfold univ_surj_nt; cbn.
    set (coeq := mk_Coequalizer _ _ _ _ _).
    apply (CoequalizerCommutes coeq).
  Qed.

  Lemma univ_surj_nt_ax_pw x  : p x · univ_surj_nt x = f x .
  Proof.
    now rewrite <- univ_surj_nt_ax.
  Qed.


  Lemma univ_surj_nt_ax_pw_pw x c : (p x · univ_surj_nt x) c = f x c.
  Proof.
    now rewrite <- univ_surj_nt_ax.
  Qed.

  Lemma univ_surj_nt_unique : ∏ g  (H : nat_trans_comp _ _ _ p  g = f)
                                b, g b = univ_surj_nt b.
  Proof.
    intros g hg b.
    apply nat_trans_eq_pointwise.
    unfold univ_surj_nt.
    set (coeq := mk_Coequalizer _ _ _ _ _).
    use (isCoequalizerOutUnique _ _ _ _ (isCoequalizer_Coequalizer coeq)).
    apply hg.
  Qed.

End LiftEpiNatTrans.

(**   Quotient functors .

Let C be a category
Let R be a functor from C to Set.

Let X be an object of C
Let tilde a family of equivalence relations on RX satisfying
if [x tilde y] and [f : X -> Y], then [f(x) tilde f(y)].

Then we can define [R'] as a functor which to any X associates [R'X = RX mod tilde]
Moreover, there is an epimorphism [pr_quot_functor : R -> R']

 *)
Section QuotientFunctor.

  Context { D:precategory}.
  Variable (R:functor D HSET).

  (** This is [tilde] *)
  Variable (hequiv : ∏ (d:D),eqrel (pr1hSet (R d))).

  (** The relations satisfied by [hequiv (tilde)] *)
  Hypothesis (congru: ∏ (x y:D) (f:D⟦ x,  y⟧), iscomprelrelfun (hequiv x) (hequiv y) (#R f)).

  (** Definition of the quotient functor *)
  (* not using setquotinset directly because as isasetsetquot is not opaque it would make
     computation slow in some cases (see issue 548) *)
  Definition quot_functor_ob (d:D) :hSet.
  Proof.
    mkpair.
    - apply (setquot (hequiv d)).
    - abstract (apply isasetsetquot).
  Defined.

  Definition quot_functor_mor (d d' : D) (f : D ⟦d, d'⟧)
    : HSET ⟦quot_functor_ob d, quot_functor_ob d' ⟧ :=
    setquotfun (hequiv d) (hequiv d') (#R f) (congru d d' f).

  Definition quot_functor_data : functor_data D HSET := tpair _ _ quot_functor_mor.

  Lemma is_functor_quot_functor_data : is_functor quot_functor_data.
  Proof.
    split.
    - intros a; simpl.
      apply funextfun.
      intro c.
      apply (surjectionisepitosets (setquotpr _));
        [now apply issurjsetquotpr | apply isasetsetquot|].
      intro x; cbn.
      now rewrite (functor_id R).
    - intros a b c f g; simpl.
      apply funextfun; intro x.
      apply (surjectionisepitosets (setquotpr _));
        [now apply issurjsetquotpr | apply isasetsetquot|].
      intro y; cbn.
      now rewrite (functor_comp R).
  Qed.

  Definition quot_functor  : functor D HSET := tpair _ _ is_functor_quot_functor_data.

  Definition pr_quot_functor_data : ∏ x , HSET ⟦R x, quot_functor x⟧ :=
    fun x a => setquotpr _ a.

  Lemma is_nat_trans_pr_quot_functor : is_nat_trans _ _ pr_quot_functor_data.
  Proof.
    red; intros; apply idpath.
  Qed.

  Definition pr_quot_functor : (nat_trans R  quot_functor) := (_ ,, is_nat_trans_pr_quot_functor).

  Lemma isEpi_pw_pr_quot_functor : ∏ x, isEpi  (pr_quot_functor x).
  Proof.
    intros a z f g eqfg.
    apply funextfun.
    intro x.
    eapply surjectionisepitosets.
    apply  issurjsetquotpr.
    apply setproperty.
    intro u.
    apply toforallpaths in eqfg.
    apply eqfg.
  Qed.

  Lemma isEpi_pr_quot_functor : isEpi (C:=functor_precategory _ _ has_homsets_HSET) pr_quot_functor.
  Proof.
    apply is_nat_trans_epi_from_pointwise_epis.
    apply isEpi_pw_pr_quot_functor.
  Qed.

  Lemma weqpathsinpr_quot_functor X x y : hequiv X x y ≃ pr_quot_functor X x = pr_quot_functor X y.
  Proof.
    apply (weqpathsinsetquot (hequiv X)).
  Qed.

End QuotientFunctor.