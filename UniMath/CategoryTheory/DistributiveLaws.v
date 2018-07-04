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

Definition is_distr_law {C C' D D' : precategory} (F : functor C D) (F' : functor C' D') (H : functor C' C) (K : functor D' D) (t : ∏ x : ob C', (functor_composite H F) x -->  (functor_composite F' K) x) := is_nat_trans _ _ t.

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
  Definition is_conjugate1 {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') :=
    ∏ (A : D) (B : C) (f : (L A) --> B),
    φ_adj h' (pr1 σ A · #H f) = #K (φ_adj h f) · pr1 τ B.

  Definition is_conjugate2 {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') :=
    ∏ (A : D) (B : C) (g : A --> R B),
    pr1 σ A · #H (φ_adj_inv h g) = φ_adj_inv h' (#K g · pr1 τ B ).

  Locate "×".

  Definition is_conjugate {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) (τ : DistrLaw K H R R') :=
    is_conjugate1 h h' σ τ × is_conjugate2 h h' σ τ.

  Definition σ_from_τ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (τ : DistrLaw K H R R') :=
    λ A : D, φ_adj_inv h' (#K (pr1 (unit_from_are_adjoints h) A) · pr1 τ (L A)).

  Definition τ_from_σ {C C' D D' : precategory}  {L : functor D C} {R : functor C D} {L' : functor D' C'} {R' : functor C' D'}  {H : functor C C'} {K : functor D D' } (h : are_adjoints L R) (h' : are_adjoints L' R') (σ : DistrLaw L' L K H) :=
    λ B : C, φ_adj h' (pr1 σ (R B) · #H (pr1 (counit_from_are_adjoints h) B)).



End Conjugates.

‌‌
