(** Author : Hichem Saghrouni
Internship at IRIT, 2018
Under the supervision of Ralph Matthes *)

Require Import UniMath.CategoryTheory.All.

Section DefDistrLaw.

(*
Variables C C' D D' : precategory.
Variable F : functor C D.
Variable F' : functor C' D'.
Variable H : functor C' C.
Variable K : functor D' D.
*)

  Definition DistrLaw {C C' D D' : precategory} (F : functor C D) (F' : functor C' D') (H : functor C' C) (K : functor D' D) : UU := nat_trans (functor_composite H F) (functor_composite F' K).

Definition DistrLaw_data_type {C C' D D' : precategory} (F : functor C D) (F' : functor C' D') (H : functor C' C) (K : functor D' D) : UU :=  ∏ x : ob C', (functor_composite H F) x -->  (functor_composite F' K) x.


Definition is_distr_law {C C' D D' : precategory} (F : functor C D) (F' : functor C' D') (H : functor C' C) (K : functor D' D) (t :  DistrLaw_data_type F F' H K) := is_nat_trans _ _ t.

End DefDistrLaw.

Print DistrLaw.

Section OperationsDistrLaws.

  Definition comp_distr_laws {C C' C'' D D' D'' : precategory} {F : functor C D} {F' : functor C' D'}  {F'' : functor C'' D''} {H : functor C' C} {H' : functor C'' C'} {K : functor D' D} {K' : functor D'' D'} (lambda : DistrLaw F F' H K) (lambda' : DistrLaw F' F'' H' K') : DistrLaw F F'' (functor_composite H' H ) (functor_composite K' K).
  Proof.
    red.
    apply (nat_trans_comp (α_functor _ _ _)).
    use (nat_trans_comp _ (α_functor _ _ _)).
    apply (nat_trans_comp (pre_whisker H' lambda)).
    apply (nat_trans_comp (α_functor_inv _ _ _)).
    exact (post_whisker lambda' K).
    Defined.



  Definition id_distr_law  {C D : precategory} (F : functor C D) : DistrLaw F F (functor_identity C) (functor_identity D).
  Proof.
    red.
    apply (nat_trans_comp (λ_functor _)).
    apply ρ_functor_inv.
  Defined.

  Lemma comp_distr_laws_assoc {C C' C'' C''' D D' D'' D''' : precategory} {F : functor C D} {F' : functor C' D'}  {F'' : functor C'' D''} {F''' : functor C''' D'''} {H : functor C' C} {H' : functor C'' C'} {H'' : functor C''' C''} {K : functor D' D} {K' : functor D'' D'} {K'' : functor D''' D''} (hs : has_homsets D) (lambda : DistrLaw F F' H K) (lambda' : DistrLaw F' F'' H' K') (lambda'' : DistrLaw F'' F''' H'' K'') :
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
    apply pathsinv0.
    apply assoc.
    (*fin variante rewrite*)
    apply cancel_precomposition.
    apply pathsinv0.
    etrans.
    apply functor_comp.
    apply cancel_precomposition.
    apply idpath.
  Qed.

  (*lois unitaires : composition avec l'identité, idF neutre à gauche et à droite*)

  Definition id_distr_law_left {C D : precategory} (F : functor C D) :
    ∏ (C' D' : precategory) (F' : functor C' D') (H : functor C' C) (K : functor D' D) (hs : has_homsets D) (lambda : DistrLaw F F' H K),
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
    rewrite id_right.
    apply idpath.
  Qed.

  Locate "·".

    Definition id_distr_law_right {C' D' : precategory} (F' : functor C' D') :
    ∏ (C D : precategory) (F : functor C D) (H : functor C' C) (K : functor D' D) (hs : has_homsets D) (lambda : DistrLaw F F' H K),
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
    repeat rewrite id_right.
    etrans.
    apply cancel_precomposition.
    apply functor_id.
    apply id_right.
  Qed.

End OperationsDistrLaws.

Section Conjugates.

  Locate "-->".
  Print φ_adj.
  Print Adjunctions.φ_adj.
  (* Condition 3.11a *)
  Definition are_conjugates {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') : UU :=
    ∏ (A : D) (B : C) (f : (L A) --> B),
    φ_adj h' (pr1 σ A · #H f) = #K (φ_adj h f) · pr1 τ B.

  (* Condition 3.11b *)
  Definition are_conjugates' {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') : UU :=
    ∏ (A : D) (B : C) (g : A --> R B),
    pr1 σ A · #H (φ_adj_inv h g) = φ_adj_inv h' (#K g · pr1 τ B ).

  Locate "×".

(*
  Definition are_conjugates {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') :=
    coprod (are_conjugates1 h h' σ τ) (are_conjugates2 h h' σ τ).
 *)

  Lemma isaprop_are_conjugates  {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') (hs: has_homsets D') : isaprop (are_conjugates h h' σ τ).
  Proof.
    apply impred; intro d.
    apply impred; intro c.
    apply impred; intro f.
    apply hs.
  Qed.

  Lemma isaprop_are_conjugates'  {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') (hs: has_homsets C') : isaprop (are_conjugates' h h' σ τ).
  Proof.
    apply impred; intro d.
    apply impred; intro c.
    apply impred; intro g.
    apply hs.
  Qed.

  Lemma are_conjugates_is_are_conjugates'  {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') (hsC': has_homsets C') (hsD': has_homsets D'): are_conjugates h h' σ τ = are_conjugates' h h' σ τ.
  Proof.
    apply propositionalUnivalenceAxiom.
    - apply isaprop_are_conjugates.
      assumption.
    - apply isaprop_are_conjugates'.
      assumption.
    - (* direction from left to right *)
      admit.
    - (* direction from right to left *)
      admit.
Admitted.


  Definition σ_data_from_τ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') : DistrLaw_data_type L' L K H
    :=
    λ A : D, φ_adj_inv h' (#K (pr1 (unit_from_are_adjoints h) A) · pr1 τ (L A)).

  Definition σ_from_τ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') : DistrLaw L' L K H.
  Proof.
    apply (mk_nat_trans (functor_composite K L') (functor_composite L H) (σ_data_from_τ h h' τ)).
    red.
    intros d d' f.
    unfold σ_data_from_τ.
    etrans.
    apply pathsinv0.
    simpl.
    apply  φ_adj_inv_natural_precomp.
    (*simpl.*)
    apply pathsinv0.
    etrans.
    apply pathsinv0.
    simpl.
    apply  φ_adj_inv_natural_postcomp.
    apply maponpaths.
    apply pathsinv0.
    etrans.
    rewrite assoc.
    (*
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
      (*égal par définition*)
      (*replace (# R' (# H (# L f))) with ( # (H ∙ R') (#L f)). + preuve que l'on peut remplacer, ie trouver un chemin entre les deux *)
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
    etrans.
    set (Hη := nat_trans_ax (unit_from_are_adjoints h)).
    apply Hη.
    apply idpath.
  Defined.

  (*Definition σ_data_from_τ_from_σ_from_τ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') :
    DistrLaw_data_type L' L K H
    := pr1 (σ_from_τ h h' τ).*)
 (*
Coercion σ_data_from_τ_from_σ_from_τ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') (σ : (σ_from_τ h h' τ)) := pr1 σ.*)


Lemma σ_from_τ_is_conjugate {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (hs : has_homsets C') (τ : DistrLaw K H R R') : are_conjugates' h h' (σ_from_τ h h' τ) τ.
Proof.
  red.
  intros A B g.
  unfold σ_from_τ.
  simpl.
  unfold  σ_data_from_τ.
  set (η := (unit_from_are_adjoints h)).
  etrans.
  apply pathsinv0.
  apply φ_adj_inv_natural_postcomp.
  apply maponpaths.
  set (Hτ := nat_trans_ax τ).
  etrans.
  rewrite <- assoc.
  apply cancel_precomposition.
  apply pathsinv0.
  apply Hτ.
  rewrite assoc.
  apply cancel_postcomposition.
  change (# (R ∙ K) (φ_adj_inv h g)) with (# K (# R (φ_adj_inv h g))).
  etrans.
  apply pathsinv0.
  use functor_comp.
  apply maponpaths.
  Locate "·".
  change (pr1 η A · # R (φ_adj_inv h g)) with (φ_adj h (φ_adj_inv h g)).
  apply φ_adj_after_φ_adj_inv.
Qed.



Definition τ_data_from_σ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) : DistrLaw_data_type K H R R'
  :=
    λ B : C, φ_adj h' (pr1 σ (R B) · #H (pr1 (counit_from_are_adjoints h) B)).

Lemma adjuncts_mutually_inverse1 {C D : precategory} {A : D} {B : C} {L : functor D C} {R : functor C D} (h : are_adjoints L R) (f : L A --> B) (g : A --> R B) : f = φ_adj_inv h g -> φ_adj h f = g.

Proof.
  intro p.


End Conjugates.

‌‌
