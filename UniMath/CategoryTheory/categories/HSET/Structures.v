(** * Other structures in [HSET] *)

(** ** Contents

  - Natural numbers object ([NNO_HSET])
  - Exponentials ([Exponentials_HSET])
  - Construction of exponentials for functors into HSET
    ([Exponentials_functor_HSET])
  - Kernel pairs ([kernel_pair_HSET])
  - Effective epis ([EffectiveEpis_HSET])
  - Split epis with axiom of choice ([SplitEpis_HSET])
  - Forgetful [functor] to [type_precat]

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA. (* flip *)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.AxiomOfChoice.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.NNO.
Require Import UniMath.CategoryTheory.SubobjectClassifier.
Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.covyoneda.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Monics.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.

Local Open Scope cat.

(** ** Natural numbers object ([NNO_HSET]) *)

Lemma isNNO_nat : isNNO TerminalHSET natHSET (λ _, 0) S.
Proof.
  intros X z s.
  use unique_exists.
  + intros n.
    induction n as [|_ n].
    * exact (z tt).
    * exact (s n).
  + now split; apply funextfun; intros [].
  + now intros; apply isapropdirprod; apply setproperty.
  + intros q [hq1 hq2].
    apply funextfun; intros n.
    induction n as [|n IH].
    * now rewrite <- hq1.
    * cbn in *; now rewrite (toforallpaths _ _ _ hq2 n), IH.
Qed.

Definition NNO_HSET : NNO TerminalHSET.
Proof.
  use mk_NNO.
  - exact natHSET.
  - exact (λ _, 0).
  - exact S.
  - exact isNNO_nat.
Defined.

(** ** Exponentials ([Exponentials_HSET]) *)

Section exponentials.

(** Define the functor: A -> _^A *)
Definition exponential_functor (A : HSET) : functor HSET HSET.
Proof.
use tpair.
+ exists (hset_fun_space A); simpl.
  intros b c f g; apply (λ x, f (g x)).
+ abstract (use tpair;
  [ intro x; now (repeat apply funextfun; intro)
  | intros x y z f g; now (repeat apply funextfun; intro)]).
Defined.

(** This checks that if we use constprod_functor2 the flip is not necessary *)
Lemma are_adjoints_constprod_functor2 A :
  are_adjoints (constprod_functor2 BinProductsHSET A) (exponential_functor A).
Proof.
use tpair.
- use tpair.
  + use tpair.
    * intro x; simpl; apply dirprodpair.
    * abstract (intros x y f; apply idpath).
  + use tpair.
    * intros X fx; apply (pr1 fx (pr2 fx)).
    * abstract (intros x y f; apply idpath).
- abstract (use tpair;
  [ intro x; simpl; apply funextfun; intro ax; reflexivity
  | intro b; apply funextfun; intro f; apply idpath]).
Defined.

Lemma Exponentials_HSET : Exponentials BinProductsHSET.
Proof.
intro a.
exists (exponential_functor a).
use tpair.
- use tpair.
  + use tpair.
    * intro x; simpl; apply flip, dirprodpair.
    * abstract (intros x y f; apply idpath).
  + use tpair.
    * intros x xf; simpl in *; apply (pr2 xf (pr1 xf)).
    * abstract (intros x y f; apply idpath).
- abstract (use tpair;
  [ now intro x; simpl; apply funextfun; intro ax; reflexivity
  | now intro b; apply funextfun; intro f]).
Defined.

End exponentials.

(** ** Construction of exponentials for functors into HSET *)

(** This section defines exponential in [C,HSET] following a slight
variation of Moerdijk-MacLane (p. 46, Prop. 1).

The formula for [C,Set] is G^F(f)=Hom(Hom(f,−)×id(F),G) taken from:

http://mathoverflow.net/questions/104152/exponentials-in-functor-categories
*)
Section exponentials_functor_cat.

Variable (C : precategory) (hsC : has_homsets C).

Let CP := BinProducts_functor_precat C _ BinProductsHSET has_homsets_HSET.
Let cy := covyoneda _ hsC.

(* Defined Q^P *)
Local Definition exponential_functor_cat (P Q : functor C HSET) : functor C HSET.
Proof.
use tpair.
- use tpair.
  + intro c.
    use hSetpair.
    * apply (nat_trans (BinProduct_of_functors C _ BinProductsHSET (cy c) P) Q).
    * abstract (apply (isaset_nat_trans has_homsets_HSET)).
  + simpl; intros a b f alpha.
    apply (BinProductOfArrows _ (CP (cy a) P) (CP (cy b) P)
                           (# cy f) (identity _) · alpha).
- abstract (
    split;
      [ intros c; simpl; apply funextsec; intro a;
        apply (nat_trans_eq has_homsets_HSET); cbn; unfold prodtofuntoprod; intro x;
        apply funextsec; intro f;
        destruct f as [cx Px]; simpl; unfold covyoneda_morphisms_data;
        now rewrite id_left
      | intros a b c f g; simpl; apply funextsec; intro alpha;
        apply (nat_trans_eq has_homsets_HSET); cbn; unfold prodtofuntoprod; intro x;
        apply funextsec; intro h;
        destruct h as [cx pcx]; simpl; unfold covyoneda_morphisms_data;
        now rewrite assoc ]).
Defined.

Local Definition eval (P Q : functor C HSET) :
  nat_trans (BinProductObject _ (CP P (exponential_functor_cat P Q)) : functor _ _) Q.
Proof.
use tpair.
- intros c ytheta; set (y := pr1 ytheta); set (theta := pr2 ytheta);
  simpl in *.
  use (theta c).
  exact (identity c,,y).
- abstract (
    intros c c' f; simpl;
    apply funextfun; intros ytheta; destruct ytheta as [y theta];
    cbn; unfold prodtofuntoprod;
    unfold covyoneda_morphisms_data;
    assert (X := nat_trans_ax theta);
    assert (Y := toforallpaths _ _ _ (X c c' f) (identity c,, y));
    eapply pathscomp0; [|apply Y]; cbn; unfold prodtofuntoprod;
    now rewrite id_right, id_left).
Defined.

(* This could be made nicer without the big abstract blocks... *)
Lemma Exponentials_functor_HSET : Exponentials CP.
Proof.
intro P.
use left_adjoint_from_partial.
- apply (exponential_functor_cat P).
- intro Q; simpl; apply eval.
- intros Q R φ; simpl in *.
  use tpair.
  + use tpair.
    * { use mk_nat_trans.
        - intros c u; simpl.
          use mk_nat_trans.
          + simpl; intros d fx.
            apply (φ d (dirprodpair (pr2 fx) (# R (pr1 fx) u))).
          + intros a b f; simpl; cbn; unfold prodtofuntoprod.
            apply funextsec; intro x.
            etrans;
              [|apply (toforallpaths _ _ _ (nat_trans_ax φ _ _ f)
                                     (dirprodpair (pr2 x) (# R (pr1 x) u)))]; cbn.
              repeat (apply maponpaths).
              assert (H : # R (pr1 x · f) = # R (pr1 x) · #R f).
              { apply functor_comp. }
              unfold prodtofuntoprod.
              simpl (pr1 _); simpl (pr2 _).
              apply maponpaths.
              apply (eqtohomot H u).
        - intros a b f; cbn.
          apply funextsec; intros x; cbn.
          apply subtypeEquality;
            [intros xx; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|].
          apply funextsec; intro y; apply funextsec; intro z; cbn.
          repeat apply maponpaths;  unfold covyoneda_morphisms_data.
          assert (H : # R (f · pr1 z) = # R f · # R (pr1 z)).
          { apply functor_comp. }
          apply pathsinv0.
          now etrans; [apply (toforallpaths _ _ _ H x)|].
      }
    * abstract (
        apply (nat_trans_eq has_homsets_HSET); cbn; intro x;
        apply funextsec; intro p;
        apply maponpaths;
        assert (H : # R (identity x) = identity (R x));
          [apply functor_id|];
        induction p as [t p]; apply maponpaths; simpl;
        now apply pathsinv0; eapply pathscomp0; [apply (toforallpaths _ _ _ H p)|]).
  + abstract (
    intros [t p]; apply subtypeEquality; simpl;
    [intros x; apply (isaset_nat_trans has_homsets_HSET)|];
    apply (nat_trans_eq has_homsets_HSET); intros c;
    apply funextsec; intro rc;
    apply subtypeEquality;
    [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl;
    rewrite p; cbn; clear p; apply funextsec; intro d; cbn;
    apply funextsec; intros [t0 pd]; simpl;
    assert (HH := toforallpaths _ _ _ (nat_trans_ax t c d t0) rc);
    cbn in HH; rewrite HH; cbn; unfold covyoneda_morphisms_data;
    unfold prodtofuntoprod;
    now rewrite id_right).
Qed.

End exponentials_functor_cat.

(** ** Kernel pairs ([kernel_pair_HSET]) *)

(* proof by Peter, copied from TypeTheory.Auxiliary.Auxiliary *)
Lemma pullback_HSET_univprop_elements {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    (ep : p1 · f = p2 · g)
    (pb : isPullback f g p1 p2 ep)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
Proof.
  intros a b e.
  set (Pb := (mk_Pullback _ _ _ _ _ _ pb)).
  apply iscontraprop1.
  - apply invproofirrelevance; intros [ab [ea eb]] [ab' [ea' eb']].
    apply subtypeEquality; simpl.
      intros x; apply isapropdirprod; apply setproperty.
    use (@toforallpaths unitset _ (λ _, ab) (λ _, ab') _ tt).
    use (MorphismsIntoPullbackEqual pb);
    apply funextsec; intros []; cbn;
    (eapply @pathscomp0; [ eassumption | apply pathsinv0; eassumption]).
  - use (_,,_).
    use (_ tt).
    use (PullbackArrow Pb (unitset : HSET)
      (λ _, a) (λ _, b)).
    apply funextsec; intro; exact e.
    simpl; split.
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr1 Pb unitset).
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr2 Pb unitset).
Defined.


Section kernel_pair_Set.

  Context  {A B:HSET}.
  Variable (f: HSET ⟦A,B⟧).


  Definition kernel_pair_HSET : kernel_pair f.
    red.
    apply PullbacksHSET.
  Defined.

  Local Notation g := kernel_pair_HSET.

  (** Formulation in the categorical language of the universal property
      enjoyed by surjections (univ_surj) *)
  Lemma isCoeqKernelPairSet (hf:issurjective f) :
    isCoequalizer _ _ _ (PullbackSqrCommutes g).
  Proof.
    intros.
    red.
    intros C u equ.
    assert (hcompat :   ∏ x y : pr1 A, f x = f y → u x = u y).
    {
      intros x y eqfxy.
      assert (hpb:=pullback_HSET_univprop_elements
                     (PullbackSqrCommutes g) (isPullback_Pullback g) x y eqfxy).
      assert( hpb' := pr2 (pr1 hpb)); simpl in hpb'.
      etrans.
      eapply pathsinv0.
      apply maponpaths.
      exact (pr1 hpb').
      eapply pathscomp0.
      apply toforallpaths in equ.
      apply equ.
      cbn.
      apply maponpaths.
      exact (pr2 hpb').
    }
    use (unique_exists (univ_surj (setproperty C) _ _ _ hf)).
    - exact u.
    - exact hcompat.
    - simpl.
      apply funextfun.
      intros ?.
      apply univ_surj_ax.
    - intros ?. apply has_homsets_HSET.
    - intros ??; simpl.
      apply funextfun.
      use univ_surj_unique.
      simpl in X.
      apply toforallpaths in X.
      exact X.
  Qed.
End kernel_pair_Set.

(** ** Effective epis ([EffectiveEpis_HSET]) *)

Lemma EffectiveEpis_HSET : EpisAreEffective HSET.
Proof.
  red.
  clear.
  intros A B f epif.
  exists (kernel_pair_HSET f).
  apply isCoeqKernelPairSet.
  now apply EpisAreSurjective_HSET.
Qed.

(** ** Split epis with axiom of choice ([SplitEpis_HSET]) *)

Lemma SplitEpis_HSET : AxiomOfChoice_surj -> EpisAreSplit HSET.
Proof.
  intros axC A B f epif.
  apply EpisAreSurjective_HSET,axC in epif.
  unshelve eapply (hinhfun _ epif).
  intro h.
  exists (pr1 h).
  apply funextfun.
  exact (pr2 h).
Qed.

(** ** Forgetful [functor] to [type_precat] *)

Definition forgetful_HSET : functor HSET type_precat.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + exact pr1.
    + exact (λ _ _, idfun _).
  - split.
    + intro; reflexivity.
    + intros ? ? ? ? ?; reflexivity.
Defined.

(** This functor is conservative; it reflects isomorphisms. *)

Lemma conservative_forgetful_HSET : conservative forgetful_HSET.
Proof.
  unfold conservative.
  intros a b f is_iso_forget_f.
  refine (hset_equiv_is_iso a b (weqpair f _)).
  apply (type_iso_is_equiv _ _ (isopair _ is_iso_forget_f)).
Defined.

(** ** Subobject classifier *)

Definition hProp_set : hSet := (_,, isasethProp).

Lemma isaprop_hfiber_monic {A B : hSet} (f : HSET⟦A, B⟧) (isM : isMonic f) :
  isPredicate (hfiber f).
Proof.
  intro; apply incl_injectivity, MonosAreInjective_HSET; assumption.
Qed.

(* Require Import UniMath.Foundations.All. *)
(* Require Import UniMath.MoreFoundations.All. *)

Local Definition const_htrue {X : hSet} : HSET⟦X, hProp_set⟧ :=
  (fun _ => htrue : hProp_set).

Local Lemma hProp_eq_unit (p : hProp) : p -> p = htrue.
Proof.
  intro pp.
  apply weqtopathshProp, weqimplimpl.
  - intro; exact tt.
  - intro; assumption.
  - apply propproperty.
  - apply propproperty.
Qed.

(** Existence of the pullback square
    <<
      X -------> TerminalHSET
      V              V
    m |              | true
      V     ∃!       V
      Y - - - - -> hProp
    >>
    Uniqueness proven below.
  *)
Definition subobject_classifier_HSET_pullback {X Y : HSET}
  (m : Monic HSET X Y) :
    ∑ (chi : HSET ⟦ Y, hProp_set ⟧)
    (H : m · chi = TerminalArrow TerminalHSET X · const_htrue),
      isPullback chi const_htrue m (TerminalArrow TerminalHSET X) H.
Proof.
  exists (fun z => (hfiber (pr1 m) z,, isaprop_hfiber_monic (pr1 m) (pr2 m) z)).
  use tpair.
  + apply funextfun; intro.
    apply hProp_eq_unit; cbn.
    use hfiberpair.
    * assumption.
    * reflexivity.
  + (** The aforementioned square is a pullback *)
    cbn beta.
    unfold isPullback; cbn.
    intros Z f g H.
    use iscontrpair.
    * use tpair.
      -- (** The hypothesis H states that that each [f x] is in the image of [m],
              and since [m] is monic (injective), this assignment extends to a map
              [Z -> X] defined by [z ↦ m^-1 (f z)]. *)
          intro z.
          eapply hfiberpr1.
          eapply eqweqmap.
          ++ apply pathsinv0.
            apply (maponpaths pr1 (toforallpaths _ _ _ H z)).
          ++ exact tt.
      -- split.
          ++ (** The first triangle commutes by definition of the above map:
                [m] sends the preimage [m^-1 (f z)] to [f z]. *)
            apply funextfun; intro z; cbn.
            apply hfiberpr2.
          ++ (** All maps to the terminal object are equal *)
            apply proofirrelevance, impred.
            intro; apply isapropunit.
    * intro.
      apply subtypeEquality.
      -- intro.
          apply isapropdirprod.
          ++ apply (setproperty (hset_fun_space _ _)).
          ++ apply (setproperty (hset_fun_space _ unitset)).
      -- cbn.
          apply funextsec; intro; cbn.
          (** Precompose with [m] and use the commutative square *)
          apply (invweq (weqpair _ (MonosAreInjective_HSET m (MonicisMonic _ m) _ _))).
          eapply pathscomp0.
          ++ apply (toforallpaths _ _ _ (pr1 (pr2 t))).
          ++ apply pathsinv0.
             apply hfiberpr2.
Defined.

(** For any subset [s : Y -> hProp], the carrier [∑ y : Y, s y] is a pullback
    of [s] with the constantly-true arrow. *)
Lemma HSET_carrier_is_pullback {Y : HSET} (chi : HSET ⟦ Y, hProp_set ⟧) :
  Pullback chi (@const_htrue unitHSET).
Proof.
  use mk_Pullback.
  - exact (carrier_subset chi).
  - exact (pr1carrier _).
  - exact (TerminalArrow TerminalHSET _).
  - apply funextfun; intro yy.
    apply hProp_eq_unit; cbn.
    apply (pr2 yy).
  - cbn.
    intros pb' h k H.
    use iscontrpair.
    + use tpair.
      * intro p.
        use tpair.
        -- exact (h p).
        -- apply toforallpaths in H; cbn.
           specialize (H p); cbn in H.
           abstract (rewrite H; exact tt).
      * split; [reflexivity|].
        apply proofirrelevance, hlevelntosn, iscontrfuntounit.
    + intro.
      apply subtypeEquality'; [|apply isapropdirprod; apply setproperty].
      apply funextfun; intro.
      apply subtypeEquality'; [|apply propproperty].
      refine (_ @ toforallpaths _ _ _ (pr1 (pr2 t)) x).
      reflexivity.
Defined.

Lemma hfiber_in_hfiber :
  ∏ Z W (g : Z -> W) (w : W) (z : hfiber g w), hfiber g (g (hfiberpr1 _ _ z)).
Proof.
  intros.
  use hfiberpair.
  - exact (hfiberpr1 _ _ z).
  - reflexivity.
Qed.

Definition subobject_classifier_HSET : subobject_classifier TerminalHSET.
Proof.
  unfold subobject_classifier.
  exists hProp_set.
  exists const_htrue.
  intros ? ? m.

  use iscontrpair.

  - (** The image of m *)
    apply subobject_classifier_HSET_pullback.
  - intro O'.
    apply subtypeEquality.
    + intro.
      apply Propositions.isaproptotal2.
      * intro; apply isaprop_isPullback.
      * intros; apply proofirrelevance, setproperty.
    + (** If the following is a pullback square,
          <<
            X ------- ! ---> unit
            |                 |
            |                 |
            V                 V
            Y -- pr1 O' --> hProp
          >>
          then [pr1 O' = hfiber m].
       *)

      assert (eq : m · pr1 O' ~ m · (fun z => (hfiber (pr1 m) z,, isaprop_hfiber_monic (pr1 m) (pr2 m) z : pr1hSet hProp_set))).
      {
        apply toforallpaths.
        refine (pr1 (pr2 O') @ _).
        apply (!pr1 (pr2 (subobject_classifier_HSET_pullback m))).
      }

      apply funextfun; intro y.
      apply weqtopathshProp, weqimplimpl.
      * intro isO.

        (** We know that [carrier (pr1 O')] is a pullback of [pr1 O'] and [const_htrue].
            By hypothesis, X is as well. Thus, we have a canonical isomorphism
            [carrier (pr1 O') -> X], which commutes with the pullback projections.
            In particular, the following triangle commutes:
            <<
            >>
         *)

        pose (PBO' := mk_Pullback (pr1 O') (@const_htrue unitHSET) X m (TerminalArrow TerminalHSET X) (pr1 (pr2 O')) (pr2 (pr2 O'))).
        pose (PBC := HSET_carrier_is_pullback (pr1 O')).
        pose (pbiso := pullbackiso PBC PBO').

        use hfiberpair.
        -- exact (morphism_from_z_iso _ _ _ (pr1 pbiso) (y,, isO)).
        -- replace (pr1 m (morphism_from_z_iso _ _ _ (pr1 pbiso) (y,, isO))) with (((pr1 pbiso) · pr1 m) (y,, isO)); [|reflexivity].
          Check (pr1 (pr2 pbiso)).
          replace (pr1 m) with (PullbackPr1 PBO'); [|reflexivity].
          rewrite (pr1 (pr2 pbiso)).
          reflexivity.
      * intros fib.
        apply (eqweqmap (maponpaths pr1 (maponpaths (pr1 O') (pr2 fib)))).
        apply (eqweqmap (maponpaths pr1 (eq (hfiberpr1 _ _ fib)))).
        apply hfiber_in_hfiber.
      * apply propproperty.
      * apply propproperty.
Qed.