(** * Composition and inverses of (adjoint) equivalences of precategories *)

(** ** Contents

  - Preliminaries
  - Composition
  - Inverses
 *)

(** Ported from UniMath/TypeTheory, could use more cleanup *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.

Require Import UniMath.CategoryTheory.Equivalences.Core.

Local Open Scope cat.
Local Open Scope cat_deprecated.

(** ** Preliminaries *)

Lemma is_iso_comp_is_iso {C : precategory} {a b c : ob C}
  (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : is_iso f -> is_iso g -> is_iso (f ;; g).
Proof.
  intros Hf Hg.
  apply (is_iso_comp_of_isos (isopair f Hf) (isopair g Hg)).
Defined.

Lemma functor_is_iso_is_iso {C C' : precategory} (F : functor C C')
    {a b : ob C} (f : C ⟦a,b⟧) (fH : is_iso f) : is_iso (#F f).
Proof.
  apply (functor_on_iso_is_iso _ _ F _ _ (isopair f fH)).
Defined.

Coercion left_adj_from_adj_equiv (X Y : precategory) (K : functor X Y)
         (HK : adj_equivalence_of_precats K) : is_left_adjoint K := pr1 HK.

(** ** Equivalences *)

Variables D1 D2 : precategory.
Variable F : functor D1 D2.
Variable GG : adj_equivalence_of_precats F.

Let G : functor D2 D1 := right_adjoint GG.
Let η := unit_from_left_adjoint GG.
Let ε := counit_from_left_adjoint GG.
Let ηinv a := iso_inv_from_iso (unit_pointwise_iso_from_adj_equivalence GG a).
Let εinv a := iso_inv_from_iso (counit_pointwise_iso_from_adj_equivalence GG a).


Lemma right_adj_equiv_is_ff : fully_faithful G.
Proof.
  intros c d.
  set (inv := (fun f : D1 ⟦G c, G d⟧ => εinv _ ;; #F f ;; ε _ )).
  simpl in inv.
  apply (gradth _ inv ).
  - intro f. simpl in f. unfold inv.
    assert (XR := nat_trans_ax ε). simpl in XR.
    rewrite <- assoc.
    etrans. apply maponpaths. apply XR.
    rewrite assoc.
    etrans. apply maponpaths_2. apply iso_after_iso_inv.
    apply id_left.
  - intro g.
    unfold inv.
    do 2 rewrite functor_comp.
    intermediate_path ((# G (inv_from_iso (counit_pointwise_iso_from_adj_equivalence GG c)) ;; ηinv _ ) ;; (η _ ;; # G (# F g)) ;; # G (ε d)).
    + do 4 rewrite <- assoc.
      apply maponpaths.
      do 2 rewrite assoc.
      etrans.
      2: do 2 apply maponpaths_2; eapply pathsinv0, iso_after_iso_inv.
      refine (_ @ assoc _ _ _).
      exact (!id_left _).
    + assert (XR := nat_trans_ax η). simpl in XR. rewrite <- XR. clear XR.
      do 3 rewrite <- assoc.
      etrans. do 3 apply maponpaths. apply  triangle_id_right_ad. rewrite id_right.
      rewrite assoc.
      etrans.
      2: apply id_left.
      apply maponpaths_2.
      etrans. apply maponpaths_2. apply functor_on_inv_from_iso.
      assert (XR := triangle_id_right_ad (pr2 (pr1 GG))); simpl in XR.
      unfold ηinv; simpl.
      pose (XRR := maponpaths pr1 (iso_inv_of_iso_comp _ _ _ _ (unit_pointwise_iso_from_adj_equivalence GG ((adj_equivalence_inv GG) c)) (functor_on_iso G (counit_pointwise_iso_from_adj_equivalence GG c)) )).
      simpl in XRR.
      etrans.
      apply (! XRR); clear XRR.
      apply pathsinv0, inv_iso_unique'.
      simpl. cbn. unfold precomp_with.
      rewrite id_right. apply XR.
Defined.

Lemma right_adj_equiv_is_ess_sur : essentially_surjective G.
Proof.
  intro d.
  apply hinhpr.
  exists (F d).
  exact (ηinv d).
Defined.

(** ** Composition *)

Section eqv_comp.

  Context {A B C : precategory}
          {hsA : has_homsets A}
          {hsB : has_homsets B}
          {hsC : has_homsets C}
          {F : functor A B}
          {F' : functor B C}.

  Hypothesis HF : adj_equivalence_of_precats F.
  Hypothesis HF' : adj_equivalence_of_precats F'.

  Definition comp_adj_equivalence_of_precats
    : adj_equivalence_of_precats (functor_composite F F').
  Proof.
    exists (is_left_adjoint_functor_composite HF HF').
    use tpair.
    - intro.
      apply is_iso_comp_is_iso.
      + apply (pr1 (pr2 HF)).
      + simpl.
        refine (eqweqmap (maponpaths is_iso _) _).
        refine (_ @ !id_right _).
        exact (!id_left _).
        apply functor_is_iso_is_iso, (pr1 (pr2 HF')).
    - cbn. intro. apply is_iso_comp_is_iso.
      +
        refine (eqweqmap (maponpaths is_iso _) _).
        refine (_ @ !id_left _).
        refine (_ @ !id_left _).
        exact (!id_right _).
        apply functor_is_iso_is_iso, (pr2 (pr2 HF)).
      + apply (pr2 (pr2 HF')).
  Defined.
End eqv_comp.

(** ** Inverses *)

Section eqv_inv.

  Context {A B : precategory}
          {hsA : has_homsets A}
          {hsB : has_homsets B}
          {F : functor A B}.

  Hypothesis adEquivF : adj_equivalence_of_precats F.

  Let η : functor_precategory _ _ hsA ⟦ _ , _ ⟧ := unit_from_left_adjoint adEquivF.
  Let ε : functor_precategory _ _ hsB ⟦ _ , _ ⟧ := counit_from_left_adjoint adEquivF.
  Let G := right_adjoint adEquivF.

  Let ηiso := unit_iso_from_adj_equivalence_of_precats hsA adEquivF.
  Let εiso := counit_iso_from_adj_equivalence_of_precats hsB adEquivF.


  Lemma form_adjunction_inv :
  form_adjunction G F (inv_from_iso εiso) (inv_from_iso ηiso).
  Proof.
    split.
    - intro b.
      apply (pre_comp_with_iso_is_inj _ _ _ _ (#G ((pr1 εiso : nat_trans _ _ )  b))).
      + apply (functor_is_iso_is_iso G).
        apply is_functor_iso_pointwise_if_iso. apply pr2.
      + etrans. apply assoc.
        etrans. apply maponpaths_2. eapply pathsinv0. apply functor_comp.
        etrans. apply maponpaths_2. apply maponpaths.
                apply (nat_trans_eq_pointwise (iso_inv_after_iso εiso)).
        etrans. apply maponpaths_2. apply functor_id.
        etrans. apply id_left.
        apply (pre_comp_with_iso_is_inj _ _ _ _ (((pr1 ηiso : nat_trans _ _ ) (G b)))).
        * apply is_functor_iso_pointwise_if_iso. apply pr2.
        * etrans. apply (nat_trans_eq_pointwise (iso_inv_after_iso ηiso)).
          apply pathsinv0.
          etrans. apply assoc.
          etrans. apply id_right.
          assert (XR := triangle_id_right_ad (pr2 (pr1 adEquivF))).
          apply XR.
    - intro a.
      apply (pre_comp_with_iso_is_inj _ _ _ _ (((pr1 εiso : nat_trans _ _ ) _))).
      * apply is_functor_iso_pointwise_if_iso. apply pr2.
      * etrans. apply assoc.
        etrans. apply maponpaths_2.
          apply (nat_trans_eq_pointwise (iso_inv_after_iso εiso)).
        etrans. apply id_left.
        apply (pre_comp_with_iso_is_inj _ _ _ _ (#F ((pr1 ηiso : nat_trans _ _ ) a))).
        { apply (functor_is_iso_is_iso F).
          apply is_functor_iso_pointwise_if_iso. apply pr2.
        }
        etrans. eapply pathsinv0. apply functor_comp.
        etrans. apply maponpaths. apply (nat_trans_eq_pointwise (iso_inv_after_iso ηiso )).
        etrans. apply functor_id.
        apply pathsinv0.
        rewrite id_right.
        apply triangle_id_left_ad.
  Qed.

  Definition is_left_adjoint_inv : is_left_adjoint G.
  Proof.
    use tpair.
    - apply F.
    - use tpair.
      exists (pr1 (iso_inv_from_iso εiso)).
      exact (pr1 (iso_inv_from_iso ηiso)).
      apply form_adjunction_inv.
  Defined.

  Definition adj_equivalence_of_precats_inv
    : adj_equivalence_of_precats G.
  Proof.
    exists is_left_adjoint_inv.
    split;
      intro;
      use (transportb is_iso (id_right _));
      apply is_iso_inv_from_iso.
  Defined.

End eqv_inv.