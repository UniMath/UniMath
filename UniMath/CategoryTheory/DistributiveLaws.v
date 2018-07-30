(** Author : Hichem Saghrouni
Internship at IRIT, 2018
Under the supervision of Ralph Matthes *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Adjunctions.

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
  (*début variante à rewrite assoc*)
  eapply pathscomp0. (*etrans.*)
  { apply pathsinv0.
    apply assoc.
    (*fin variante rewrite*)
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
Defined.

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
Defined.

(*  Locate "-->".
  Print φ_adj.
  Print Adjunctions.φ_adj. *)

(* Condition 3.11a *)
Definition are_conjugates {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'}{H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R')
           (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') : UU :=
  ∏ (A : D) (B : C) (f : (L A) --> B),
  φ_adj h' (nat_trans_data_from_nat_trans σ A · #H f) = #K (φ_adj h f) · nat_trans_data_from_nat_trans τ B.

(* Condition 3.11b *)
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
Defined.


Definition σ_data_from_τ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
           {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
           (h : are_adjoints L R) (h' : are_adjoints L' R')
           (τ : DistrLaw K H R R') : DistrLaw_data L' L K H :=
  λ A : D, φ_adj_inv h' (#K (unit_from_are_adjoints h A) · nat_trans_data_from_nat_trans τ (L A)).

Definition σ_from_τ {C C' D D' : precategory} {L : functor D C} {R : functor C D}
  {L' : functor D' C'} {R' : functor C' D'} {H : functor C C'} {K : functor D D' }
  (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') : DistrLaw L' L K H.
Proof.
  apply (mk_nat_trans _ _ (σ_data_from_τ h h' τ)).
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

(* Proofs that τ_data_from_σ is a distributive law, and that τ_from_σ and σ are conjugates are left to the reader. *)


End Conjugates.

Section Liftings.

Definition is_lifting {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} (H: functor C D) (HH: functor (FunctorAlg F hsC) (FunctorAlg G hsD)): UU.
Proof.
  set (UF := forget_algebras F hsC).
  set (UG := forget_algebras G hsD).
  exact (UF ∙ H = HH ∙ UG).
Defined.

Print FunctorAlg.

Definition lifting_from_distr_law_data {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H): functor_data (FunctorAlg F hsC) (FunctorAlg G hsD).
Proof.
  use mk_functor_data.
  simpl.
  intro Aa.
  set (A := alg_carrier _ Aa).
  set (a := alg_map _ Aa).
  simpl in a.
  set (B := H A).
  set (b := nat_trans_data_from_nat_trans lambda A · (# H a)).
  use tpair.
  exact B.
  exact b.

  simpl.
  intros Aa Bb.
  intro h.
  set (H_lambda_h := #H h).
  unfold algebra_mor.
  simpl.
  use tpair.
  apply H_lambda_h.

  unfold is_algebra_mor.
  simpl.
  unfold H_lambda_h.
  set (ax := nat_trans_ax lambda).
  apply pathsinv0.
  etrans.
  rewrite assoc.
  apply cancel_postcomposition.
  apply ax.

  rewrite <- assoc.
  apply pathsinv0.
  rewrite <- assoc.
  apply cancel_precomposition.
  set (h_commutes := algebra_mor_commutes _ _ _ h).
  rewrite <- functor_comp.
  apply pathsinv0.
  change (# (F ∙ H) h) with (# H (# F h)).
  etrans.
  apply pathsinv0.
  apply (functor_comp H).

  apply maponpaths.
  apply pathsinv0.
  apply h_commutes.
Defined.


Definition lifting_from_distr_law {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} {H: functor C D} (lambda : DistrLaw G F H H): functor (FunctorAlg F hsC) (FunctorAlg G hsD).
Proof.
  set (HH_data := lifting_from_distr_law_data hsC hsD lambda).
  use (mk_functor HH_data).
  red.
  split.
  - red.
    intro Aa.
    unfold HH_data.
    unfold lifting_from_distr_law_data.
    simpl.
    UniMath.MoreFoundations.Tactics.show_id_type.
    apply algebra_mor_eq.
    Locate algebra_mor_eq.
    + assumption.
    + simpl.
      apply functor_id.
  - red.
    intros Aa Bb Cc f g.
    unfold HH_data.
    unfold lifting_from_distr_law_data.
    simpl.
    UniMath.MoreFoundations.Tactics.show_id_type.
    apply algebra_mor_eq.
    + assumption.
    + simpl.
      apply functor_comp.
Defined.



Lemma lifting_from_distr_law_is_lifting {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D) {F: functor C C} {G: functor D D} (H: functor C D) (lambda : DistrLaw G F H H):
  is_lifting hsC hsD H (lifting_from_distr_law hsC hsD lambda ).
Proof.
  unfold is_lifting.
  set (Hλ := lifting_from_distr_law hsC hsD lambda).
  (*UniMath.MoreFoundations.Tactics.show_id_type.*)
  Locate "⟶".
  apply functor_eq.
  - assumption.
  - UniMath.MoreFoundations.Tactics.show_id_type.
    apply idpath.
Defined.

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
  Locate InitialArrow.

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