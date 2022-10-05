(** ***************************************************************

Contents:
 - Category of coalgebras over an endofunctor.
 - Dual of Lambek's lemma: if (A,α) is terminal coalgebra, α is an isomorphism.

******************************************************************)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

Section Coalgebra_Definition.

  Context {C : category} (F : functor C C).

  Definition coalgebra_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ x, x --> F x).
    - exact (λ x y hx hy f, hx · #F f = f · hy).
  Defined.

  Definition coalgebra_disp_cat_id_comp
    : disp_cat_id_comp C coalgebra_disp_cat_ob_mor.
  Proof.
    split.
    - intros x hx ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x y z f g hx hy hz hf hg ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc.
      rewrite hf.
      rewrite !assoc'.
      rewrite hg.
      apply idpath.
  Qed.

  Definition coalgebra_disp_cat_data : disp_cat_data C
    := coalgebra_disp_cat_ob_mor ,, coalgebra_disp_cat_id_comp.

  Definition coalgebra_disp_cat_axioms
    : disp_cat_axioms C coalgebra_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition coalgebra_disp_cat : disp_cat C
    := coalgebra_disp_cat_data ,, coalgebra_disp_cat_axioms.

  Definition CoAlg_category : category
    := total_category coalgebra_disp_cat.

  Definition coalgebra_ob : UU := ob CoAlg_category.


  Definition coalg_carrier (X : coalgebra_ob) : C := pr1 X.
  Local Coercion coalg_carrier : coalgebra_ob >-> ob.

  Definition coalg_map (X : coalgebra_ob) : C ⟦X, F X ⟧ := pr2 X.

  (** A homomorphism of F-coalgebras (F A, α : C ⟦A, F A⟧) and (F B, β : C ⟦B, F B⟧)
    is a morphism f : C ⟦A, B⟧ s.t. the below diagram commutes.
<<
         f
     A -----> B
     |        |
     | α      | β
     |        |
     V        V
    F A ---> F B
        F f
>>
*)

  Definition is_coalgebra_mor (X Y : coalgebra_ob) (f : coalg_carrier X --> coalg_carrier Y) : UU
    := coalg_map X · #F f = f · coalg_map Y.

  Definition coalgebra_mor (X Y : coalgebra_ob) : UU := CoAlg_category⟦X,Y⟧.
  Coercion mor_from_coalgebra_mor {X Y : coalgebra_ob} (f : coalgebra_mor X Y) : C⟦X, Y⟧ := pr1 f.

  Lemma coalgebra_mor_commutes {X Y : coalgebra_ob} (f : coalgebra_mor X Y)
    : coalg_map X · #F f = pr1 f · coalg_map Y.
  Proof.
    exact (pr2 f).
  Qed.

  Definition coalgebra_homo_eq {X Y : coalgebra_ob}
             (f g : coalgebra_mor X Y) : (f : C ⟦X, Y⟧) = g ≃ f = g.
  Proof.
    apply invweq.
    apply subtypeInjectivity.
    intro. apply homset_property.
  Defined.

End Coalgebra_Definition.

Section Lambek_dual.
(** Dual of Lambeks Lemma : If (A,α) is terminal F-coalgebra, then α is an iso *)

Context (C : category)
        (F : functor C C)
        (X : coalgebra_ob F).

Local Notation F_CoAlg := (CoAlg_category F).

Context (isTerminalX : isTerminal F_CoAlg X).

Definition TerminalX : Terminal F_CoAlg := make_Terminal _ isTerminalX.

Local Notation α := (coalg_map F (TerminalObject TerminalX)).
Local Notation A := (coalg_carrier F (TerminalObject TerminalX)).

(** FX := (FA,Fα) is also an F-coalgebra *)
Definition FX : ob F_CoAlg := tpair _ (F A) (#F α).

(** By terminality there is an arrow α' : FA → A, s.t.:
<<
         α'
    FA ------> A
    |          |
    | Fα       | α
    V          V
   FFA ------> FA
         Fα'
>>
  commutes *)

Definition f : F_CoAlg ⟦FX, TerminalX⟧ := (@TerminalArrow F_CoAlg TerminalX FX).

Definition α' : C ⟦F A, A⟧ := mor_from_coalgebra_mor F f.

Definition αα'_mor : coalgebra_mor F X X.
Proof.
  exists (α · α').
  simpl.
  rewrite <- assoc.
  apply cancel_precomposition.
  rewrite functor_comp.
  apply (coalgebra_mor_commutes F f).
Defined.

Definition αα'_idA : α · α' = identity A
  := maponpaths pr1 (TerminalEndo_is_identity (T:=TerminalX) αα'_mor).

Lemma α'α_idFA : α' · α = identity (F A).
Proof.
  rewrite <- functor_id.
  rewrite <- αα'_idA.
  rewrite functor_comp.
  unfold α'.
  apply pathsinv0.
  apply (coalgebra_mor_commutes F f).
Defined.

Lemma terminalcoalgebra_isiso : is_iso α.
Proof.
  apply (is_iso_qinv α α').
  split.
  - exact αα'_idA.
  - exact α'α_idFA.
Defined.

Definition terminalcoalgebra_iso : iso A (F A) := make_iso α terminalcoalgebra_isiso.

End Lambek_dual.
