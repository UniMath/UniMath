(**
Facts about set valued functors

- epimorphic natural transformations are pointwise epimorphic
- epimorphic natural transformations enjoy a universal property similar to
surjections (univ_surj_nt)

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.limits.coequalizers.


Lemma is_pointwise_epi_from_set_nat_trans_epi (C:precategory)
      (F G : functor C hset_precategory) (f:nat_trans F G)
      (h:isEpi (C:=functor_precategory C _ has_homsets_HSET) f)
  : Π (x:C), isEpi (f x).
Proof.
  apply (Pushouts_pw_epi (D:=hset_Precategory)).
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
commute provided that for any set X, any x,y in X, if p x = p y then f x = f y

This property comes from the fact that p is an effective epimorphism.
*)
Section LiftEpiNatTrans.

  Context { CC:precategory}.
  Local Notation C_SET :=  (functor_precategory CC HSET has_homsets_HSET).


  Context {A B C:functor CC HSET} (p:nat_trans A B)
          (f:nat_trans A C).

  Hypothesis (comp_epi: Π (X:CC)  (x y: pr1hSet (A X)),
                        p X x =  p X y -> f X x = f X y).

  Hypothesis (surjectivep : isEpi (C:=C_SET) p).

  Lemma EffectiveEpis_Functor_HSET : EpisAreEffective C_SET.
  Proof.
    intros F G m isepim.
    apply (isEffectivePw (D:=hset_Precategory)).
    intro x.
    apply EffectiveEpis_HSET.
    apply (Pushouts_pw_epi (D:=hset_Precategory)
                           PushoutsHSET_from_Colims).
    assumption.
  Qed.

  Definition univ_surj_nt : nat_trans B C.
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

  Lemma univ_surj_nt_ax_pw x  : p x ;; univ_surj_nt x = f x .
  Proof.
    now rewrite <- univ_surj_nt_ax.
  Qed.


  Lemma univ_surj_nt_ax_pw_pw x c : (p x ;; univ_surj_nt x) c = f x c.
  Proof.
    now rewrite <- univ_surj_nt_ax.
  Qed.

  Lemma univ_surj_nt_unique : Π g  (H : nat_trans_comp _ _ _ p  g = f)
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
