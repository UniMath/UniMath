(** Author : Hichem Saghrouni
Internship at IRIT, 2018 *)

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

End DefDistrLaw.

Print DistrLaw.

Section OperationsDistrLaws.

  Definition comp_distr_laws {C C' C'' D D' D'' : precategory} {F : functor C D} {F' : functor C' D'}  {F'' : functor C'' D''} {H : functor C' C} {H' : functor C'' C'} {K : functor D' D} {K' : functor D'' D'} (lambda : DistrLaw F F' H K) (lambda' : DistrLaw F' F'' H' K') : DistrLaw F F'' (functor_composite H' H ) (functor_composite K' K).
  Proof.
    red.
    apply (nat_trans_comp (α_functor _ _ _)).
    refine (nat_trans_comp _ (α_functor _ _ _)).
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

(*Lemma comp_distr_laws_assoc : .*)

End OperationsDistrLaws.