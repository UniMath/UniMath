(**

From signatures to monads

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.lists.

(* S : SIG *)
(* |->  # some hacking needed *)
(* functor(S) : functor [Set,Set] [Set,Set] *)
(* |->  # exists because func(S) is omega-cocont *)
(* Initial (Id + functor(S)) *)
(* |->  # see LiftingInitial.v *)
(* I:= Initial (HSS(func(S), \theta) *)
(* |->  # see MonadsFromSubstitutionSystems.v *)
(* M := Monad_from_HSS(I)    # *)
Section SigToMonad.

Local Notation "'HSET2'":= ([HSET, HSET, has_homsets_HSET]) .

Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Local Definition ProductsHSET2 : Products HSET2.
Proof.
apply (Products_functor_precat _ _ ProductsHSET).
Defined.

Local Definition CoproductsHSET2 : Coproducts HSET2.
Proof.
apply (Coproducts_functor_precat _ _ CoproductsHSET).
Defined.

Local Lemma has_exponentials_HSET2 : has_exponentials  ProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

(* Specialized notations for HSET2 *)

(* Notation "' x" := (omega_cocont_constant_functor _ _ has_homsets_HSET2 x) *)
(*                     (at level 10) : cocont_functor_hset_scope. *)

Local Notation "'Id'" := (omega_cocont_functor_identity _ has_homsets_HSET2).

Local Notation "F * G" :=
  (omega_cocont_product_functor _ _ ProductsHSET2 _
     has_exponentials_HSET2 has_homsets_HSET2 has_homsets_HSET2 F G).

Local Notation "F + G" :=
  (omega_cocont_coproduct_functor _ _ ProductsHSET2 CoproductsHSET2
     has_homsets_HSET2 has_homsets_HSET2 F G).


Definition Sig : UU := list (list nat).

Let precomp_option := omega_cocont_pre_composition_functor _ _ _
                        (option_functor HSET CoproductsHSET TerminalHSET) has_homsets_HSET has_homsets_HSET cats_LimsHSET.

(* This would have been nice, but it adds an extra Id in the end *)
(* Local Definition SigToFunctor_helper2 (n : nat) : omega_cocont_functor HSET2 HSET2 := *)
(*   omega_cocont_iter_functor has_homsets_HSET2 (precomp_option) n. *)

Local Fixpoint SigToFunctor_helper2 (n : nat) : omega_cocont_functor HSET2 HSET2 := match n with
  | O => Id
  | S O => precomp_option
  | S n' => let G := omega_cocont_pre_composition_functor _ _ _
                       (option_functor HSET CoproductsHSET TerminalHSET) has_homsets_HSET has_homsets_HSET cats_LimsHSET
               (* is this order correct???? *)
            in omega_cocont_functor_composite has_homsets_HSET2 G (SigToFunctor_helper2 n')
  end.
(* Proof. *)
(* intro n. *)
(* induction n as [|_ F]. *)
(* - apply Id. *)
(* - *)
(* set (G := (omega_cocont_pre_composition_functor _ _ _ *)
(*             (option_functor HSET CoproductsHSET TerminalHSET) has_homsets_HSET has_homsets_HSET cats_LimsHSET)). *)
(* (* is this order correct???? *) *)
(* apply (omega_cocont_functor_composite has_homsets_HSET2 G F). *)
(* Defined. *)

Local Definition SigToFunctor_helper : list nat -> omega_cocont_functor HSET2 HSET2.
Proof.
intro l.
generalize (map_list SigToFunctor_helper2 l).
apply foldr1_list.
- intros F G.
  apply (F * G).
- apply Id.
Defined.

Definition SigToFunctor : Sig -> omega_cocont_functor HSET2 HSET2.
Proof.
use foldr_list.
- intros l F.
  apply (SigToFunctor_helper l + F).
- apply Id.
Defined.

(* Test lambda calculus *)
Section test_lam.

Infix "::" := (cons_list nat).
Notation "[]" := (nil_list nat) (at level 0, format "[]").

(* The signature of the lambda calculus: [[0,0],[1]] *)
Definition LamSig : Sig := cons_list (list nat) (0 :: 0 :: []) (cons_list (list nat) (1 :: []) (nil_list (list nat))).

Eval cbn in SigToFunctor LamSig.

Require Import UniMath.SubstitutionSystems.LamHSET.

Let Lam_S : Signature HSET has_homsets_HSET :=
  Lam_Sig HSET has_homsets_HSET TerminalHSET CoproductsHSET ProductsHSET.

Check (pr1 Lam_S).
Goal (pr1 Lam_S = pr1 (SigToFunctor LamSig)).
simpl.
apply subtypeEquality.
intros x.
apply isaprop_is_functor.
apply (functor_category_has_homsets HSET HSET has_homsets_HSET).
simpl.
unfold App_H, square_functor.
unfold Abs_H.
apply maponpaths.
admit.
Abort. (* equal if we add Id *)

End test_lam.

Variable (sig : Sig).

Definition SigToSignature : Signature HSET has_homsets_HSET.
Proof.
mkpair.
- apply (SigToFunctor sig).
- mkpair.
+ destruct sig as [n xs].
  induction n.
  { - destruct xs; simpl.
      mkpair.
      + simpl; intro x; destruct x as [F x]; simpl.
        mkpair.
      * simpl.
        intro y.
        apply idfun.
      *
        intros y y' f.
        simpl.
        apply idpath.
      + intros y y' f.
        apply (nat_trans_eq has_homsets_HSET).
        intro x; simpl.
        destruct y.
        destruct y'.
        simpl.
        apply idpath.
  }
  { mkpair.
    - simpl; intro y.
      mkpair.
      + admit.
      + admit.
    - admit.
  }
+ admit.
Admitted.

Definition SigInitial : Initial (FunctorAlg (Id_H HSET has_homsets_HSET CoproductsHSET SigToSignature)
                                (functor_category_has_homsets HSET HSET has_homsets_HSET)).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_coproduct_functor.
  + apply (Products_functor_precat _ _ ProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor; apply functor_category_has_homsets.
  + admit.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Admitted.

Definition SigInitialHSS : Initial (hss_precategory CoproductsHSET SigToSignature).
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, cats_LimsHSET.
- apply SigInitial.
Defined.

Definition SigToMonad : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply CoproductsHSET.
- apply SigToSignature.
- apply SigInitialHSS.
Defined.

End SigToMonad.
