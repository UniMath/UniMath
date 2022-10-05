(** * Composition and inverses of (adjoint) equivalences of precategories *)

(** ** Contents

  - Preliminaries
  - Composition
  - Inverses
  - 2 out of 3 property
  - Pairing equivalences
 *)

(** Ported from UniMath/TypeTheory, could use more cleanup *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.
Local Open Scope cat_deprecated.

(** ** Preliminaries *)

Lemma is_z_iso_comp_is_z_iso {C : category} {a b c : ob C}
  (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : is_z_isomorphism f -> is_z_isomorphism g -> is_z_isomorphism (f ;; g).
Proof.
  intros Hf Hg.
  apply (is_z_iso_comp_of_is_z_isos f g Hf Hg).
Defined.

Lemma functor_is_z_iso_is_z_iso {C C' : category} (F : functor C C')
    {a b : ob C} (f : C ⟦a,b⟧) (fH : is_z_isomorphism f) : is_z_isomorphism (#F f).
Proof.
  apply (z_iso_is_z_isomorphism (functor_on_z_iso F (make_z_iso' f fH))).
Defined.

Coercion left_adj_from_adj_equiv (X Y : category) (K : functor X Y)
         (HK : adj_equivalence_of_cats K) : is_left_adjoint K := pr1 HK.

(** ** Equivalences *)

Section A.

Variables D1 D2 : category.
Variable F : functor D1 D2.
Variable GG : adj_equivalence_of_cats F.

Let G : functor D2 D1 := right_adjoint GG.
Let η := unit_from_left_adjoint GG.
Let ε := counit_from_left_adjoint GG.
Let ηinv a := z_iso_inv_from_z_iso (unit_pointwise_z_iso_from_adj_equivalence GG a).
Let εinv a := z_iso_inv_from_z_iso (counit_pointwise_z_iso_from_adj_equivalence GG a).


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
    etrans. apply maponpaths_2. apply z_iso_after_z_iso_inv.
    apply id_left.
  - intro g.
    unfold inv.
    do 2 rewrite functor_comp.
    intermediate_path ((# G (inv_from_z_iso (counit_pointwise_z_iso_from_adj_equivalence GG c)) ;; ηinv _ ) ;; (η _ ;; # G (# F g)) ;; # G (ε d)).
    + do 4 rewrite <- assoc.
      apply maponpaths.
      do 2 rewrite assoc.
      etrans.
      2: do 2 apply maponpaths_2; eapply pathsinv0, z_iso_after_z_iso_inv.
      refine (_ @ assoc _ _ _).
      exact (!id_left _).
    + assert (XR := nat_trans_ax η). simpl in XR. rewrite <- XR. clear XR.
      do 3 rewrite <- assoc.
      etrans. do 3 apply maponpaths. apply  triangle_id_right_ad. rewrite id_right.
      rewrite assoc.
      etrans.
      2: apply id_left.
      apply maponpaths_2.
      etrans. apply maponpaths_2. apply functor_on_inv_from_z_iso.
      assert (XR := triangle_id_right_ad (pr2 (pr1 GG))); simpl in XR.
      unfold ηinv; simpl.
      pose (XRR := maponpaths pr1 (z_iso_inv_of_z_iso_comp _ _ _ (unit_pointwise_z_iso_from_adj_equivalence GG ((adj_equivalence_inv GG) c)) (functor_on_z_iso G (counit_pointwise_z_iso_from_adj_equivalence GG c)) )).
      simpl in XRR.
      etrans.
      apply (! XRR).
      clear XRR.
      apply pathsinv0, inv_z_iso_unique'.
      cbn. unfold precomp_with.
      rewrite id_right. apply XR.
Defined.

Lemma right_adj_equiv_is_ess_sur : essentially_surjective G.
Proof.
  intro d.
  apply hinhpr.
  exists (F d).
  exact (ηinv d).
Defined.

End A.

(** ** Composition *)

Section eqv_comp.

  Context {A B C : category}
          {F : functor A B}
          {F' : functor B C}.

  Hypothesis HF : adj_equivalence_of_cats F.
  Hypothesis HF' : adj_equivalence_of_cats F'.

  Definition comp_adj_equivalence_of_cats
    : adj_equivalence_of_cats (functor_composite F F').
  Proof.
    exists (is_left_adjoint_functor_composite HF HF').
    use tpair.
    - intro.
      apply is_z_iso_comp_is_z_iso.
      + apply (pr1 (pr2 HF)).
      + simpl.
        refine (eqweqmap (maponpaths is_z_isomorphism _) _).
        refine (_ @ !id_right _).
        exact (!id_left _).
        apply functor_is_z_iso_is_z_iso, (pr1 (pr2 HF')).
    - cbn. intro. apply is_z_iso_comp_is_z_iso.
      +
        refine (eqweqmap (maponpaths is_z_isomorphism _) _).
        refine (_ @ !id_left _).
        refine (_ @ !id_left _).
        exact (!id_right _).
        apply functor_is_z_iso_is_z_iso, (pr2 (pr2 HF)).
      + apply (pr2 (pr2 HF')).
  Defined.
End eqv_comp.

(** ** Inverses *)

Section eqv_inv.

  Local Definition nat_z_iso_to_pointwise_z_iso {A B : category} {F G : functor A B}
    (n : nat_z_iso F G) (x : ob A) : z_iso (F x) (G x) := make_z_iso' _ (pr2 n x).

  Local Lemma nat_z_iso_inv_after_nat_z_iso {A B : category} {F G : functor A B}
    (n : nat_z_iso F G) : ∏ x, (nat_z_iso_to_pointwise_z_iso n) x · (nat_z_iso_inv n) x = identity _.
  Proof.
    intro; apply z_iso_inv_after_z_iso.
  Qed.

  Context {A B : category} {F : functor A B}
          (adEquivF : adj_equivalence_of_cats F).

  Local Notation η := (unit_from_left_adjoint adEquivF).
  Local Notation ε := (counit_from_left_adjoint adEquivF).
  Local Notation G := (right_adjoint (pr1 adEquivF)).

  Local Notation ηiso := (unit_nat_z_iso_from_adj_equivalence_of_cats adEquivF).
  Local Notation εiso := (counit_nat_z_iso_from_adj_equivalence_of_cats adEquivF).

  Lemma form_adjunction_inv :
    form_adjunction _ F (nat_z_iso_inv εiso) (nat_z_iso_inv ηiso).
  Proof.
    split.
    - intro b.
      (** Use the right triangle identity that we already know *)
      refine (_ @ triangle_id_right_ad (pr2 (pr1 adEquivF)) b).

      (** Transform it by precomposing with the inverse isos *)
      apply (pre_comp_with_z_iso_is_inj' (f:=#G (nat_z_iso_to_pointwise_z_iso εiso b)));
      [apply (functor_is_z_iso_is_z_iso G), z_iso_is_z_isomorphism |].

      (** Cancel the isos *)
      unfold adjunit; unfold adjcounit.
      unfold pr2, pr1.
      rewrite assoc.
      rewrite <- functor_comp.
      unfold left_functor; unfold pr1.
      rewrite nat_z_iso_inv_after_nat_z_iso.
      rewrite functor_id.
      rewrite id_left.
      rewrite assoc.

      (** Again, precompose with the inverse iso *)
      use (pre_comp_with_z_iso_is_inj'
             (f:=(nat_z_iso_to_pointwise_z_iso ηiso (G b))));
        [apply z_iso_is_z_isomorphism; rewrite z_iso_inv_after_z_iso|].
      rewrite (nat_z_iso_inv_after_nat_z_iso ηiso).

      refine (!triangle_id_right_ad (pr2 (pr1 adEquivF)) _ @ _).
      refine (!id_left _ @ _).
      repeat rewrite assoc.
      do 2 rewrite <- assoc. (* This is inelegant... *)
      apply (maponpaths (fun f => f · _)).
      apply (!triangle_id_right_ad (pr2 (pr1 adEquivF)) _).
    - (** Same proof, just backwards *)
      intro a.
      refine (_ @ triangle_id_left_ad (pr2 (pr1 adEquivF)) a).

      apply (pre_comp_with_z_iso_is_inj'
                                      (f:=nat_z_iso_to_pointwise_z_iso εiso (F a)));
        [apply z_iso_is_z_isomorphism; rewrite z_iso_inv_after_z_iso|].
      rewrite assoc.
      rewrite (nat_z_iso_inv_after_nat_z_iso εiso).
      rewrite id_left.

      apply (pre_comp_with_z_iso_is_inj' (f:=#F (nat_z_iso_to_pointwise_z_iso ηiso a)));
        [apply (functor_is_z_iso_is_z_iso F), z_iso_is_z_isomorphism |].
      unfold adjunit; unfold adjcounit.
      unfold right_functor.
      unfold pr2, pr1.
      refine (_ @ !assoc _ _ _).
      refine (!functor_comp F _ _ @ _).
      rewrite (nat_z_iso_inv_after_nat_z_iso ηiso).
      rewrite functor_id.

      refine (!triangle_id_left_ad (pr2 (pr1 adEquivF)) _ @ _).
      refine (!id_left _ @ _).
      repeat rewrite assoc.
      do 2 rewrite <- assoc. (* This is inelegant... *)
      apply (maponpaths (fun f => f · _)).
      apply (!triangle_id_left_ad (pr2 (pr1 adEquivF)) _).
  Qed.

  Definition is_left_adjoint_inv : is_left_adjoint G.
  Proof.
    use tpair.
    - apply F.
    - use tpair.
      exists (pr1 (nat_z_iso_inv εiso)).
      exact (pr1 (nat_z_iso_inv ηiso)).
      apply form_adjunction_inv.
  Defined.

  Definition adj_equivalence_of_cats_inv
    : adj_equivalence_of_cats G.
  Proof.
    exists is_left_adjoint_inv.
    split; intro; unfold is_left_adjoint_inv; cbn.
    - apply (is_z_iso_inv_from_z_iso(_,,dirprod_pr2 (pr2 adEquivF) a)).
    - apply (is_z_iso_inv_from_z_iso(_,,dirprod_pr1 (pr2 adEquivF) b)).
  Defined.

End eqv_inv.

(** Closure under natural isomorphisms *)
Definition nat_z_iso_equivalence_of_cats
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (α : F ⟹ G)
           (Hα : is_nat_z_iso α)
           (HF : adj_equivalence_of_cats F)
  : equivalence_of_cats C₁ C₂.
Proof.
  use make_equivalence_of_cats.
  - use make_adjunction_data.
    + exact G.
    + exact (right_adjoint HF).
    + exact (nat_trans_comp
               _ _ _
               (adjunit HF)
               (post_whisker α _)).
    + exact (nat_trans_comp
               _ _ _
               (pre_whisker _ (nat_z_iso_inv (make_nat_z_iso _ _ α Hα)))
               (adjcounit HF)).
  - split.
    + intro x ; cbn.
      use is_z_iso_comp_of_is_z_isos.
      * apply (unit_nat_z_iso_from_adj_equivalence_of_cats HF).
      * apply functor_is_z_iso_is_z_iso.
        apply Hα.
    + intro x ; cbn.
      use is_z_iso_comp_of_is_z_isos.
      * apply (is_z_iso_inv_from_z_iso(_,,(Hα (pr1 (pr1 HF) x)))).
      * apply (counit_nat_z_iso_from_adj_equivalence_of_cats HF).
Defined.

Definition nat_iso_adj_equivalence_of_cats
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (α : F ⟹ G)
           (Hα : is_nat_z_iso α)
           (HF : adj_equivalence_of_cats F)
  : adj_equivalence_of_cats G
  := adjointificiation (nat_z_iso_equivalence_of_cats α Hα HF).

(**
 2 out of 3 property
 *)
Section TwoOutOfThree.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₂)
          (G : C₂ ⟶ C₃)
          (H : C₁ ⟶ C₃)
          (ν : nat_z_iso (F ∙ G) H).

  Definition two_out_of_three_first
             (HG : adj_equivalence_of_cats G)
             (HH : adj_equivalence_of_cats H)
    : adj_equivalence_of_cats F.
  Proof.
    pose (ζ := make_nat_z_iso
                 (F ∙ functor_identity _)
                 (F ∙ (G ∙ right_adjoint HG))
                 _
                 (pre_whisker_on_nat_z_iso
                    F
                    (unit_nat_z_iso_from_adj_equivalence_of_cats HG)
                    (pr2 (unit_nat_z_iso_from_adj_equivalence_of_cats HG)))).
    use (nat_iso_adj_equivalence_of_cats
           _
           _
           (comp_adj_equivalence_of_cats
              HH
              (adj_equivalence_of_cats_inv HG))).
    - exact (nat_trans_comp
               (H ∙ right_adjoint HG)
               ((F ∙ G) ∙ right_adjoint HG)
               _
               (post_whisker
                  (nat_z_iso_inv ν)
                  (right_adjoint HG))
               (nat_z_iso_inv ζ)).
    - use is_nat_z_iso_comp.
      + use post_whisker_z_iso_is_z_iso.
        apply (nat_z_iso_inv ν).
      + apply (nat_z_iso_inv ζ).
  Defined.

  Definition two_out_of_three_second
             (HF : adj_equivalence_of_cats F)
             (HH : adj_equivalence_of_cats H)
    : adj_equivalence_of_cats G.
  Proof.
    use (nat_iso_adj_equivalence_of_cats
           _
           _
           (comp_adj_equivalence_of_cats
              (adj_equivalence_of_cats_inv HF)
              HH)).
    - exact (nat_trans_comp
               (right_adjoint HF ∙ H)
               (right_adjoint HF ∙ F ∙ G)
               G
               (pre_whisker
                  (right_adjoint HF)
                  (nat_z_iso_inv ν))
               (post_whisker
                  (counit_nat_z_iso_from_adj_equivalence_of_cats HF)
                  G)).
    - use is_nat_z_iso_comp.
      + apply (pre_whisker_on_nat_z_iso (right_adjoint HF) (nat_z_iso_inv ν)).
        apply (nat_z_iso_inv ν).
      + apply (post_whisker_z_iso_is_z_iso
                 (counit_nat_z_iso_from_adj_equivalence_of_cats HF)
                 G).
        apply (counit_nat_z_iso_from_adj_equivalence_of_cats HF).
  Defined.

  Definition two_out_of_three_comp
             (HF : adj_equivalence_of_cats F)
             (HG : adj_equivalence_of_cats G)
    : adj_equivalence_of_cats H.
  Proof.
    use (nat_iso_adj_equivalence_of_cats ν (pr2 ν)).
    exact (comp_adj_equivalence_of_cats HF HG).
  Defined.
End TwoOutOfThree.

(**
 Pairing equivalences
 *)
Section PairEquivalence.
  Context {C₁ C₁' C₂ C₂' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          (HF : adj_equivalence_of_cats F)
          (HG : adj_equivalence_of_cats G).

  Let L : category_binproduct C₁ C₂ ⟶ category_binproduct C₁' C₂'
    := pair_functor F G.

  Let R : category_binproduct C₁' C₂' ⟶ category_binproduct C₁ C₂
    := pair_functor (right_adjoint HF) (right_adjoint HG).

  Definition pair_equivalence_of_cats_unit_data
    : nat_trans_data (functor_identity _) (L ∙ R)
    := λ x, adjunit HF (pr1 x) ,, adjunit HG (pr2 x).

  Definition pair_equivalence_of_cats_unit_is_nat_trans
    : is_nat_trans
        _ _
        pair_equivalence_of_cats_unit_data.
  Proof.
    intros x y f.
    use pathsdirprod ; cbn.
    - exact (nat_trans_ax (adjunit HF) _ _ (pr1 f)).
    - exact (nat_trans_ax (adjunit HG) _ _ (pr2 f)).
  Qed.

  Definition pair_equivalence_of_cats_unit
    : functor_identity (category_binproduct C₁ C₂) ⟹ L ∙ R.
  Proof.
    use make_nat_trans.
    - exact pair_equivalence_of_cats_unit_data.
    - exact pair_equivalence_of_cats_unit_is_nat_trans.
  Defined.

  Definition pair_equivalence_of_cats_counit_data
    : nat_trans_data (R ∙ L) (functor_identity _)
    := λ x, adjcounit HF (pr1 x) ,, adjcounit HG (pr2 x).

  Definition pair_equivalence_of_cats_counit_is_nat_trans
    : is_nat_trans
        _ _
        pair_equivalence_of_cats_counit_data.
  Proof.
    intros x y f.
    use pathsdirprod ; cbn.
    - exact (nat_trans_ax (adjcounit HF) _ _ (pr1 f)).
    - exact (nat_trans_ax (adjcounit HG) _ _ (pr2 f)).
  Qed.

  Definition pair_equivalence_of_cats_counit
    : R ∙ L ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact pair_equivalence_of_cats_counit_data.
    - exact pair_equivalence_of_cats_counit_is_nat_trans.
  Defined.

  Definition pair_equivalence_of_cats
    : equivalence_of_cats
        (category_binproduct C₁ C₂)
        (category_binproduct C₁' C₂').
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact L.
      + exact R.
      + exact pair_equivalence_of_cats_unit.
      + exact pair_equivalence_of_cats_counit.
    - split.
      + intro x.
        use is_z_iso_binprod_z_iso.
        * exact (z_iso_is_z_isomorphism
                   (nat_z_iso_pointwise_z_iso
                      (unit_nat_z_iso_from_adj_equivalence_of_cats HF)
                      (pr1 x))).
        * exact (z_iso_is_z_isomorphism
                   (nat_z_iso_pointwise_z_iso
                      (unit_nat_z_iso_from_adj_equivalence_of_cats HG)
                      (pr2 x))).
      + intro x.
        use is_z_iso_binprod_z_iso.
        * exact (z_iso_is_z_isomorphism
                   (nat_z_iso_pointwise_z_iso
                      (counit_nat_z_iso_from_adj_equivalence_of_cats HF)
                      (pr1 x))).
        * exact (z_iso_is_z_isomorphism
                   (nat_z_iso_pointwise_z_iso
                      (counit_nat_z_iso_from_adj_equivalence_of_cats HG)
                      (pr2 x))).
  Defined.
End PairEquivalence.

Definition pair_adj_equivalence_of_cats
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           (HF : adj_equivalence_of_cats F)
           (HG : adj_equivalence_of_cats G)
  : adj_equivalence_of_cats (pair_functor F G)
  := adjointificiation (pair_equivalence_of_cats HF HG).
