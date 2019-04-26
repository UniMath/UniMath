(** Author : Hichem Saghrouni
Internship at IRIT, 2018
Under the supervision of Ralph Matthes

Later continued by Ralph Matthes (R.M.), see the end of this comment.

Work on the paper
HINZE, R. and WU, N., 2016. Unifying structured recursion schemes: An Extended Study. Journal of Functional Programming, vol. 26, https://doi.org/10.1017/S0956796815000258.

The purpose of this file is to formalize in UniMath the recursion scheme
presented by Hinze and Wu, with their original approach making use of
liftings and conjugates.

For this, we formalize the notions of
- Distributive Laws, which are natural transformations between
compositions of functors
- Conjugates, which induce a binary relation between distributive laws,
defined by certain identities found in this document
- Liftings, which constitute a specific type of functors between F-Algebras

These constructions finally allow us to follow the proof by Hinze and Wu
of their theorem (found under "Theorem 5.2 (Adjoint folds)" in their
paper) and thus reprove it formally.


Added by R.M.: how canonically defined liftings compose


*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

Section DefDistrLaw.

Context {C C' D D' : precategory} (F : functor C D) (F' : functor C' D')
          (H : functor C' C) (K : functor D' D).

(** the definition of Hinze and Wu - no other laws required for being considered a distributive law *)
Definition DistrLaw (*{C C' D D' : precategory} (F : functor C D) (F' : functor C' D')
  (H : functor C' C) (K : functor D' D)*) : UU :=
  nat_trans (H ∙ F) (F' ∙ K).

(** a small help for later type-checking *)
Definition DistrLaw_data (*{C C' D D' : precategory} (F : functor C D) (F' : functor C' D')
  (H : functor C' C) (K : functor D' D)*) : UU :=
  nat_trans_data (H ∙ F) (F' ∙ K).

End DefDistrLaw.


Section OperationsDistrLaws.

Definition comp_distr_laws {C C' C'' D D' D'' : precategory}{F : functor C D}{F' : functor C' D'}
  {F'' : functor C'' D''}{H : functor C' C}{H' : functor C'' C'}{K : functor D' D}{K' : functor D'' D'}
  (lambda : DistrLaw F F' H K) (lambda' : DistrLaw F' F'' H' K') :
  DistrLaw F F'' (H' ∙ H ) (K' ∙ K).
Proof.
  red.
  apply (nat_trans_comp _ _ _ (α_functor _ _ _)).
  use (nat_trans_comp _ _ _ _ (α_functor _ _ _)).
  apply (nat_trans_comp _ _ _ (pre_whisker H' lambda)).
  apply (nat_trans_comp _ _ _ (α_functor_inv _ _ _)).
  exact (post_whisker lambda' K).
Defined.



Definition id_distr_law  {C D : precategory} (F : functor C D) :
  DistrLaw F F (functor_identity C) (functor_identity D).
Proof.
  red.
  apply (nat_trans_comp _ _ _ (λ_functor _)).
  apply ρ_functor_inv.
Defined.

Lemma comp_distr_laws_assoc {C C' C'' C''' D D' D'' D''' : precategory} {F : functor C D}
      {F' : functor C' D'}  {F'' : functor C'' D''} {F''' : functor C''' D'''}
      {H : functor C' C} {H' : functor C'' C'} {H'' : functor C''' C''}
      {K : functor D' D} {K' : functor D'' D'} {K'' : functor D''' D''}
      (hs : has_homsets D) (lambda : DistrLaw F F' H K)
      (lambda' : DistrLaw F' F'' H' K') (lambda'' : DistrLaw F'' F''' H'' K'') :
  comp_distr_laws (comp_distr_laws lambda lambda') lambda'' =
                comp_distr_laws lambda (comp_distr_laws lambda' lambda'').
Proof.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  repeat rewrite id_left.
  repeat rewrite id_right.
  set (aux1 := nat_trans_ax lambda).
  (*rewrite <- assoc.*)
  (*Beginning of variant to : rewrite assoc*)
  eapply pathscomp0. (*etrans.*)
  { apply pathsinv0.
    apply assoc.
    (*End of variant to rewrite*)
  }
  apply cancel_precomposition.
  apply pathsinv0.
  etrans.
  { apply functor_comp. }
  apply cancel_precomposition.
  apply idpath.
Qed.

  (*lois unitaires : composition avec l'identité, idF neutre à gauche et à droite*)

Definition id_distr_law_left {C D : precategory} (F : functor C D) :
  ∏ (C' D' : precategory) (F' : functor C' D') (H : functor C' C) (K : functor D' D)
    (hs : has_homsets D) (lambda : DistrLaw F F' H K),
  comp_distr_laws (id_distr_law F) lambda  = lambda.
Proof.
  intros C' D'.
  intros F' H K.
  intro hs.
  intro lambda.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  repeat rewrite id_left.
  apply id_right.
Qed.

(* Locate "·". *)

Definition id_distr_law_right {C' D' : precategory} (F' : functor C' D') :
  ∏ (C D : precategory) (F : functor C D) (H : functor C' C) (K : functor D' D)
    (hs : has_homsets D) (lambda : DistrLaw F F' H K),
  comp_distr_laws lambda (id_distr_law F')  = lambda.
Proof.
  intros C D.
  intros F H K.
  intro hs.
  intro lambda.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  repeat rewrite id_left.
  rewrite id_right.
  etrans.
  { apply cancel_precomposition.
    apply functor_id.
  }
  apply id_right.
Qed.

End OperationsDistrLaws.

Section Conjugates.

Lemma adjuncts_mutually_inverse1 {C D : precategory} {A : D} {B : C}
      {L : functor D C} {R : functor C D} (h : are_adjoints L R)
      (f : L A --> B) (g : A --> R B) :
  f = φ_adj_inv h g -> φ_adj h f = g.
Proof.
  intro p.
  set (η := unit_from_are_adjoints h).
  set (ε := counit_from_are_adjoints h).
  set (triangle_right := triangle_id_right_ad h).
  change (unit_from_are_adjoints h) with η in triangle_right.
  change (counit_from_are_adjoints h) with ε in triangle_right.
  unfold φ_adj.
  assert (hyp : f = (φ_adj_inv h g)).
  - exact p.
  - rewrite hyp.
    unfold φ_adj_inv.
    rewrite functor_comp.
    change (# R (# L g)) with (# (L ∙ R) g).
    rewrite assoc.
    set (Hη := nat_trans_ax η).
    etrans.
    { apply cancel_postcomposition.
      apply pathsinv0.
      apply Hη.
    }
    rewrite <- id_right.
    rewrite <-  assoc.
    apply cancel_precomposition.
    exact (triangle_right B).
Qed.

Lemma adjuncts_mutually_inverse2 {C D : precategory} {A : D} {B : C}
      {L : functor D C} {R : functor C D} (h : are_adjoints L R)
      (f : L A --> B) (g : A --> R B) :
  φ_adj h f = g -> f = φ_adj_inv h g.
Proof.
  intro p.
  set (η := unit_from_are_adjoints h).
  set (ε := counit_from_are_adjoints h).
  set (triangle_left := triangle_id_left_ad h).
  unfold φ_adj_inv.
  assert (hyp : g = (φ_adj h f)).
  - apply pathsinv0.
    exact p.
  - rewrite hyp.
    unfold φ_adj.
    rewrite functor_comp.
    change ( # L (# R f)) with (# (R ∙ L) f).
    rewrite <- assoc.
    set (Hε := nat_trans_ax ε).
    apply pathsinv0.
    etrans.
    { apply cancel_precomposition.
      apply Hε.
    }
    rewrite <- id_left.
    rewrite assoc.
    apply cancel_postcomposition.
    exact (triangle_left A).
Qed.

(*  Locate "-->".
  Print φ_adj.
  Print Adjunctions.φ_adj. *)

(* Condition 3.11a in Hinze & Wu *)
Definition are_conjugates {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'}{H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R')
           (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') : UU :=
  ∏ (A : D) (B : C) (f : (L A) --> B),
  φ_adj h' (nat_trans_data_from_nat_trans σ A · #H f) = #K (φ_adj h f) · nat_trans_data_from_nat_trans τ B.

(* Condition 3.11b in Hinze & Wu *)
Definition are_conjugates' {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R')
           (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') : UU :=
  ∏ (A : D) (B : C) (g : A --> R B),
  nat_trans_data_from_nat_trans σ A · #H (φ_adj_inv h g) = φ_adj_inv h' (#K g · nat_trans_data_from_nat_trans τ B ).

(* Locate "×". *)


Lemma isaprop_are_conjugates {C C' D D' : precategory} {L : functor D C} {R : functor C D}
      {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
      (h : are_adjoints L R) (h' : are_adjoints L' R')
      (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') (hs: has_homsets D') :
  isaprop (are_conjugates h h' σ τ).
Proof.
  apply impred; intro d.
  apply impred; intro c.
  apply impred; intro f.
  apply hs.
Qed.

Lemma isaprop_are_conjugates'  {C C' D D' : precategory} {L : functor D C} {R : functor C D}
      {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
      (h : are_adjoints L R) (h' : are_adjoints L' R')
      (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') (hs: has_homsets C') :
  isaprop (are_conjugates' h h' σ τ).
Proof.
  apply impred; intro d.
  apply impred; intro c.
  apply impred; intro g.
  apply hs.
Qed.

Lemma are_conjugates_is_are_conjugates' {C C' D D' : precategory}
      {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}
      {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R')
      (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R')
      (hsC': has_homsets C') (hsD': has_homsets D'):
  are_conjugates h h' σ τ = are_conjugates' h h' σ τ.
Proof.
  apply propositionalUnivalenceAxiom.
  - apply isaprop_are_conjugates.
    assumption.
  - apply isaprop_are_conjugates'.
    assumption.
  - (* direction from left to right *)
    red.
    intro P.
    red in P.
    intros A B g.
    set (hyp := (P A B (φ_adj_inv h g))).
    apply adjuncts_mutually_inverse2 in hyp.
    assert (hyp2 : # K (φ_adj h (φ_adj_inv h g)) = # K g).
    + apply maponpaths.
      apply φ_adj_after_φ_adj_inv.
    + apply pathsinv0 in hyp.
      eapply pathscomp0 in hyp.
      2 : {
        apply maponpaths.
        apply cancel_postcomposition.
        apply pathsinv0.
        apply hyp2.
      }
      apply pathsinv0 in hyp.
      exact hyp.
  - (* direction from right to left *)
    red.
    intro P.
    red in P.
    intros A B f.
    set (hyp := (P A B (φ_adj h f))).
    apply (adjuncts_mutually_inverse1 h' (pr1 σ A · # H (φ_adj_inv h (φ_adj h f))) (# K (φ_adj h f) · pr1 τ B)) in hyp.
    eapply pathscomp0 in hyp.
    2 : {
      apply maponpaths.
      apply cancel_precomposition.
      apply maponpaths.
      apply pathsinv0.
      apply φ_adj_inv_after_φ_adj.
    }
    exact hyp.
Qed.


Definition σ_data_from_τ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R')
           (τ : DistrLaw K H R R') : DistrLaw_data L' L K H :=
  λ A : D, φ_adj_inv h' (#K (unit_from_are_adjoints h A) · nat_trans_data_from_nat_trans τ (L A)).

Lemma is_nat_trans_σ_data_from_τ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R')
           (τ : DistrLaw K H R R') : is_nat_trans _ _ (σ_data_from_τ h h' τ).
Proof.
  red.
  intros d d' f.
  unfold σ_data_from_τ.
  etrans.
  { apply pathsinv0.
    simpl.
    apply φ_adj_inv_natural_precomp.
  }
  (*simpl.*)
  apply pathsinv0.
  etrans.
  { apply pathsinv0.
    simpl.
    apply φ_adj_inv_natural_postcomp.
  }
  apply maponpaths.
  apply pathsinv0.
  etrans.
  rewrite assoc.
  (* Variant:
    set (Kcompax1 := pr2 K).
    set (Kcompax2 := pr2  (pr2 K)).
    unfold is_functor in Kcompax1.
    unfold functor_compax in Kcompax2.

    apply Kcompax2.
   *)
  rewrite <- functor_comp.
  2: {
    set (Hτ := nat_trans_ax τ).
    change  (# R' (# H (# L f))) with ( # (H ∙ R') (#L f)).
    (*equals by defintion*)
    (*Variant : replace (# R' (# H (# L f))) with ( # (H ∙ R') (#L f)). + proof that we can replace, ie find a path between the two*)
    rewrite <- assoc.
    apply cancel_precomposition.
    (*exact (Hτ _ _ _).*)
    apply Hτ.
  }

  rewrite assoc.
  apply cancel_postcomposition.
  change (# (R ∙ K) (# L f)) with (# K (# (L ∙ R) f)).
  etrans.
  2 : {
    use functor_comp.
  }
  apply maponpaths.
  (*apply pathsinv0.*)
  set (Hη := nat_trans_ax (unit_from_are_adjoints h)).
  apply Hη.
Defined.

Definition σ_from_τ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
  {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
  (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') : DistrLaw L' L K H.
Proof.
  apply (mk_nat_trans _ _ (σ_data_from_τ h h' τ)).
  apply is_nat_trans_σ_data_from_τ.
Defined.

Lemma σ_from_τ_is_conjugate {C C' D D' : precategory} {L : functor D C}
      {R : functor C D} {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
      (h : are_adjoints L R) (h' : are_adjoints L' R')
      (hs : has_homsets C') (τ : DistrLaw K H R R') :
  are_conjugates' h h' (σ_from_τ h h' τ) τ.
Proof.
  red.
  intros A B g.
  unfold σ_from_τ.
  simpl.
  unfold σ_data_from_τ.
  set (η := (unit_from_are_adjoints h)).
  etrans.
  { apply pathsinv0.
    apply φ_adj_inv_natural_postcomp.
  }
  apply maponpaths.
  set (Hτ := nat_trans_ax τ).
  etrans.
  { rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    apply Hτ.
  }
  rewrite assoc.
  apply cancel_postcomposition.
  change (# (R ∙ K) (φ_adj_inv h g)) with (# K (# R (φ_adj_inv h g))).
  etrans.
  { apply pathsinv0.
    use functor_comp.
  }
  apply maponpaths.
  (* Locate "·". *)
  change (nat_trans_data_from_nat_trans η A · # R (φ_adj_inv h g)) with (φ_adj h (φ_adj_inv h g)).
  apply φ_adj_after_φ_adj_inv.
Qed.

Definition τ_data_from_σ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) :
  DistrLaw_data K H R R' :=
  λ B : C, φ_adj h' (nat_trans_data_from_nat_trans σ (R B) · #H (counit_from_are_adjoints h B)).

Lemma is_nat_trans_τ_data_from_σ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) :
  is_nat_trans _ _ (τ_data_from_σ h h' σ).
Proof.
  red.
  intros c c' f.
  unfold τ_data_from_σ.
  etrans.
  { apply pathsinv0.
    simpl.
    apply φ_adj_natural_precomp.
  }
  apply pathsinv0.
  etrans.
  { apply pathsinv0.
    simpl.
    apply φ_adj_natural_postcomp.
  }
  apply maponpaths.
  etrans.
  2: {
    set (Hσ := nat_trans_ax σ).
    change  (# L' (# K (# R f))) with ( # (K ∙ L') (#R f)).
    rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply Hσ.
  }
  rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite <- assoc.
  apply cancel_precomposition.
  change (# (L ∙ H) (# R f)) with (# H (# (R ∙ L) f)).
  etrans.
  2: { apply (functor_comp H). }
  apply maponpaths.
  set (Hη := nat_trans_ax (counit_from_are_adjoints h)).
  apply pathsinv0.
  apply Hη.
Qed.

Definition τ_from_σ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) :
  DistrLaw K H R R'.
Proof.
  apply (mk_nat_trans _ _ (τ_data_from_σ h h' σ)).
  apply is_nat_trans_τ_data_from_σ.
Defined.

Lemma τ_from_σ_is_conjugate {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R') (hs : has_homsets C') (σ : DistrLaw L' L K H) : are_conjugates h h' σ (τ_from_σ h h' σ).
Proof.
  red.
  intros A B g.
  unfold τ_from_σ; simpl.
  unfold τ_data_from_σ.
  set (ε := (counit_from_are_adjoints h)).
  etrans.
  2: { apply φ_adj_natural_precomp. }
  apply maponpaths.
  etrans.
  2: { set (Hσ := nat_trans_ax σ).
    rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply Hσ.
  }
  rewrite <- assoc.
  apply cancel_precomposition.
  change (# (L ∙ H) (φ_adj h g)) with (# H (# L (φ_adj h g))).
  etrans.
  2: { apply (functor_comp H). }
  apply maponpaths.
  apply pathsinv0.
  apply φ_adj_inv_after_φ_adj.
Qed.

End Conjugates.

Section Liftings.

Definition is_lifting {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} (H: functor C D) (HH: functor (FunctorAlg F hsC) (FunctorAlg G hsD)): UU.
Proof.
  set (UF := forget_algebras F hsC).
  set (UG := forget_algebras G hsD).
  exact (UF ∙ H = HH ∙ UG).
Defined.

Definition lifting_from_distr_law_data_on_ob {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H): FunctorAlg F hsC → FunctorAlg G hsD.
Proof.
  intro Aa.
  set (A := alg_carrier _ Aa).
  set (a := alg_map _ Aa).
  set (B := H A).
  set (b := nat_trans_data_from_nat_trans lambda A · (# H a)).
  use tpair.
  - exact B.
  - exact b.
Defined.

Lemma lifting_from_distr_law_data_aux {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H)(Aa Bb : algebra_ob F)(h : algebra_mor F Aa Bb)
  : is_algebra_mor G (lifting_from_distr_law_data_on_ob hsC hsD lambda Aa)
                     (lifting_from_distr_law_data_on_ob hsC hsD lambda Bb) (#H h).
Proof.
  unfold is_algebra_mor.
  simpl.
  set (ax := nat_trans_ax lambda).
  apply pathsinv0.
  etrans.
  { rewrite assoc.
    apply cancel_postcomposition.
    apply ax. }
  rewrite <- assoc.
  apply pathsinv0.
  rewrite <- assoc.
  apply cancel_precomposition.
  set (h_commutes := algebra_mor_commutes _ _ _ h).
  rewrite <- functor_comp.
  apply pathsinv0.
  change (# (F ∙ H) h) with (# H (# F h)).
  etrans.
  { apply pathsinv0.
    apply (functor_comp H). }
  apply maponpaths.
  apply pathsinv0.
  apply h_commutes.
Qed.

Definition lifting_from_distr_law_data {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H): functor_data (FunctorAlg F hsC) (FunctorAlg G hsD).
Proof.
  use mk_functor_data.
  - apply (lifting_from_distr_law_data_on_ob hsC hsD lambda).
  - cbn.
    intros Aa Bb.
    intro h.
    unfold algebra_mor.
    use tpair.
    + exact (#H h).
    + apply lifting_from_distr_law_data_aux.
Defined.

Lemma is_functor_lifting_from_distr_law_data {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H): is_functor (lifting_from_distr_law_data hsC hsD lambda).
Proof.
  split.
  - intro Aa.
    unfold lifting_from_distr_law_data.
    cbn.
    UniMath.MoreFoundations.Tactics.show_id_type.
    apply algebra_mor_eq.
    (*Locate algebra_mor_eq.*)
    + assumption.
    + cbn.
      apply functor_id.
  - intros Aa Bb Cc f g.
    unfold lifting_from_distr_law_data.
    cbn.
    UniMath.MoreFoundations.Tactics.show_id_type.
    apply algebra_mor_eq.
    + assumption.
    + cbn.
      apply functor_comp.
Qed.

Definition lifting_from_distr_law {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H): functor (FunctorAlg F hsC) (FunctorAlg G hsD).
Proof.
  use tpair.
  - apply (lifting_from_distr_law_data hsC hsD lambda).
  - apply is_functor_lifting_from_distr_law_data.
Defined.



Lemma lifting_from_distr_law_is_lifting {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} (H: functor C D) (lambda : DistrLaw G F H H):
  is_lifting hsC hsD H (lifting_from_distr_law hsC hsD lambda ).
Proof.
  unfold is_lifting.
  set (Hλ := lifting_from_distr_law hsC hsD lambda).
  (*UniMath.MoreFoundations.Tactics.show_id_type.*)
  (*Locate "⟶".*)
  apply functor_eq.
  - assumption.
  - UniMath.MoreFoundations.Tactics.show_id_type.
    apply idpath.
Qed.

(** a simple preparation for the next lemma - strictly speaking, not even needed *)
Ltac get_sides_of_eq := match goal with |- @paths _ ?L ?R => set (left := L); set (right := R) end.

Arguments idtomor {_ _ _ } _.

(** unnamed result by Hinze & Wu, mentioned in their Sect. 3.2.1 *)
Lemma liftings_from_distr_laws_compose {C C' C'': precategory}
      (hsC: has_homsets C) (hsC': has_homsets C') (hsC'': has_homsets C'')
      {F: functor C C} {F': functor C' C'} {F'': functor C'' C''}
      {H: functor C C'} {H': functor C' C''}
      (lambda : DistrLaw F' F H H)(lambda' : DistrLaw F'' F' H' H'):
  lifting_from_distr_law hsC hsC' lambda ∙ lifting_from_distr_law hsC' hsC'' lambda' =
  lifting_from_distr_law hsC hsC'' (H := H ∙ H') (comp_distr_laws lambda' lambda).
Proof.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply functor_eq.
  { apply (has_homsets_FunctorAlg _ hsC''). }
  simpl.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  get_sides_of_eq.
  (* we have to read the expressions back, so as to get functor_data between precategories: *)
  set (left' := functor_composite_data (lifting_from_distr_law_data hsC hsC' lambda)
            (lifting_from_distr_law_data hsC' hsC'' lambda')).
  set (right' := lifting_from_distr_law_data hsC hsC'' (comp_distr_laws lambda' lambda)
   : functor_data (FunctorAlg F hsC) (FunctorAlg F'' hsC'')).
  transparent assert (okonobs: (functor_on_objects left' ~ functor_on_objects right')).
  { intro alg.
    cbn. unfold lifting_from_distr_law_data_on_ob. cbn.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply (maponpaths (λ p, tpair _ (H' (H (alg_carrier F alg))) p )).
    abstract ( repeat rewrite id_left; rewrite id_right; rewrite <- assoc; apply maponpaths; apply functor_comp ).
  }
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply (functor_data_eq_from_nat_trans _ _ _ _ okonobs).
  red.
  intros alg1 alg2 m.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply algebra_mor_eq.
  { assumption. }
  simpl.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  etrans.
  { apply cancel_precomposition.
    UniMath.MoreFoundations.Tactics.show_id_type.
    apply (idtomor_FunctorAlg_commutes _ _ _ _ (okonobs alg2)).
  }
  etrans.
  2: {
    apply cancel_postcomposition.
    UniMath.MoreFoundations.Tactics.show_id_type.
    apply pathsinv0.
    apply (idtomor_FunctorAlg_commutes _ _ _ _ (okonobs alg1)).
  }
  assert (Hyp: (idtomor (maponpaths (alg_carrier F'') (okonobs alg1)) = identity _) ×
               (idtomor (maponpaths (alg_carrier F'') (okonobs alg2)) = identity _)).
  { unfold okonobs; split.
    - etrans.
      { apply maponpaths.
        apply (maponpathscomp (λ p :
       C'' ⟦ F'' (H' (H (alg_carrier F alg1))), H' (H (alg_carrier F alg1)) ⟧,
       tpair (fun X: C'' => C'' ⟦ F'' X, X ⟧)
             (H' (H (alg_carrier F alg1))) p)
                              (alg_carrier F'')).
      }
      unfold funcomp.
      simpl.
      rewrite UniMath.MoreFoundations.PartA.maponpaths_for_constant_function.
      apply idpath.
    - etrans.
      { apply maponpaths.
        apply (maponpathscomp (λ p :
       C'' ⟦ F'' (H' (H (alg_carrier F alg2))), H' (H (alg_carrier F alg2)) ⟧,
       tpair (fun X: C'' => C'' ⟦ F'' X, X ⟧)
             (H' (H (alg_carrier F alg2))) p)
                              (alg_carrier F'')).
      }
      unfold funcomp.
      simpl.
      rewrite UniMath.MoreFoundations.PartA.maponpaths_for_constant_function.
      apply idpath.
  }
  induction Hyp as [Hyp1 Hyp2].
  rewrite Hyp1. rewrite Hyp2.
  rewrite id_right.
  apply pathsinv0.
  apply id_left.
Qed.

End Liftings.

Section AdjointFolds.

(* the conclusion of the following theorem is done after the example of [UniMath.SubstitutionSystems.GenMendlerIteration], and its proof is divided in the same way *)

Local Notation "↓ f" := (mor_from_algebra_mor _ _ _ f) (at level 3, format "↓ f").
(* in Agda mode \downarrow *)


Context {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D)
  {L: functor D C} {R: functor C D}  (h : are_adjoints L R) {CC: functor C C} {DD: functor D D}
  (μDD_Initial : Initial (FunctorAlg DD hsD))
  {σ: DistrLaw L L DD CC} {τ: DistrLaw DD CC R R} (hh: are_conjugates h h σ τ)
  {B: C} (b: CC B --> B).

Let AF := FunctorAlg CC hsC.

Definition AlgConstr (A : C) (a : CC A --> A) : AF.
Proof.
  exists B.
  exact b.
Defined.

Let μDD: D := alg_carrier _ (InitialObject μDD_Initial).
(* Locate InitialObject. *)
Let inDD: DD(μDD) --> μDD := alg_map _ (InitialObject μDD_Initial).


Definition traho_of_Hinze_Wu : L μDD --> B.
Proof.
  set (x := φ_adj_inv h ↓(InitialArrow μDD_Initial (lifting_from_distr_law hsC hsD τ (AlgConstr B b)))).
  exact x.
Defined.

Definition φ_adj_traho_of_Hinze_Wu : algebra_mor DD (InitialObject μDD_Initial)
                                                 ((lifting_from_distr_law hsC hsD τ) (AlgConstr B b)).
Proof.
  use tpair.
  - exact (φ_adj h traho_of_Hinze_Wu).
  - red.
    unfold traho_of_Hinze_Wu.
    rewrite φ_adj_after_φ_adj_inv.
    apply algebra_mor_commutes.
Defined.


Lemma traho_of_Hinze_Wu_ok : #L inDD · traho_of_Hinze_Wu =
                             nat_trans_data_from_nat_trans σ μDD · # CC traho_of_Hinze_Wu · b.
Proof.
  etrans.
  apply pathsinv0.
  use φ_adj_inv_after_φ_adj .
  exact R.
  exact h.
  apply pathsinv0.
  etrans.
  apply pathsinv0.
  use φ_adj_inv_after_φ_adj .
  exact R.
  exact h.
  apply maponpaths.

  etrans.
  use φ_adj_natural_postcomp.
  apply pathsinv0.
  etrans.
  use φ_adj_natural_precomp.
  apply pathsinv0.
  etrans.
  apply cancel_postcomposition.
  use hh .

  rewrite <- assoc.
  (*
  set (n := nat_trans_data_from_nat_trans τ B · # R b).
  set (m := alg_map DD ((lifting_from_distr_law hsC hsD τ) (AlgConstr' B b))).
  simpl in m.
  change (nat_trans_data_from_nat_trans τ B · # R b) with m.
   *)
  change (nat_trans_data_from_nat_trans τ B · # R b) with
      (alg_map DD ((lifting_from_distr_law hsC hsD τ) (AlgConstr B b))).
  (*Locate InitialArrow.*)

  apply pathsinv0.
  apply  (algebra_mor_commutes DD _ _ φ_adj_traho_of_Hinze_Wu).
Qed.

Definition φ_adj_h_x (x : C ⟦ L μDD, B ⟧)
  (Hyp: # DD (φ_adj h x) · alg_map DD ((lifting_from_distr_law hsC hsD τ)(AlgConstr B b)) =
        inDD · φ_adj h x):
  algebra_mor DD (InitialObject μDD_Initial) ((lifting_from_distr_law hsC hsD τ) (AlgConstr B b)).
Proof.
  use tpair.
  - exact (φ_adj h x).
  - red.
    apply pathsinv0.
    apply Hyp.
Defined.

Lemma φ_adj_h_x_equals_initial_arrow (x : C ⟦ L μDD, B ⟧) :
  # DD (φ_adj h x) · alg_map DD((lifting_from_distr_law hsC hsD τ)(AlgConstr B b)) =
  inDD · φ_adj h x ->
  φ_adj h x = ↓ (InitialArrow μDD_Initial ((lifting_from_distr_law hsC hsD τ) (AlgConstr B b))).
Proof.
  intro Hyp.
  set (aux := InitialArrowUnique μDD_Initial _ (φ_adj_h_x x Hyp)).
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  set (aux' := mor_from_algebra_mor _ _ _ (φ_adj_h_x x Hyp)).
  simpl in aux'.
  change (φ_adj h x) with (mor_from_algebra_mor _ _ _ (φ_adj_h_x x Hyp)).
  rewrite aux.
  apply idpath.
Qed.

(** The following formalizes Theorem 5.2 (Adjoint folds) of Hinze and Wu. *)
Theorem TheoremOfHinzeAndWu :
  iscontr (∑ x : L μDD --> B, #L inDD · x = nat_trans_data_from_nat_trans σ μDD · # CC x · b).
Proof.
  red.
  exists (traho_of_Hinze_Wu,, traho_of_Hinze_Wu_ok).

  intro t.
  induction t as [x hyp].
  assert (same: x = traho_of_Hinze_Wu).
  2: {
    apply subtypeEquality.
    + intro.
      simpl.
      apply hsC.
    + simpl.
      exact same.
  }

  etrans.
  { apply pathsinv0.
    apply (φ_adj_inv_after_φ_adj h).
  }
  etrans.
  2: {
    apply (φ_adj_inv_after_φ_adj h).
  }
  apply maponpaths.
  unfold traho_of_Hinze_Wu.
  rewrite (φ_adj_after_φ_adj_inv h).

  apply φ_adj_h_x_equals_initial_arrow.
  simpl.

  etrans.
  { rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply hh.
  }
  etrans.
  { apply pathsinv0.
    apply φ_adj_natural_postcomp.
  }
  etrans.
  2 : {
    apply φ_adj_natural_precomp.
  }
  apply maponpaths.
  apply pathsinv0.
  exact hyp.

Defined.

End AdjointFolds.
