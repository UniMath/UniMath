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
Require Import UniMath.SubstitutionSystems.ProductOfSignatures.
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

Let optionHSET := (option_functor HSET CoproductsHSET TerminalHSET).

(* This would have been nice, but it adds an extra Id in the end *)
(* Local Definition SigToFunctor_helper2 (n : nat) : omega_cocont_functor HSET2 HSET2 := *)
(*   omega_cocont_iter_functor has_homsets_HSET2 (precomp_option) n. *)

Fixpoint iter_functor1 {C : precategory} (F : functor C C) (n : nat) : functor C C := match n with
  | O => F
  | S n' => functor_composite (iter_functor F n') F
  end.

(* This constructs: _ o option^n *)
(* Local Definition precomp_option_iter (n : nat) : omega_cocont_functor HSET2 HSET2 := match n with *)
(*   | O => Id *)
(*   | S n => omega_cocont_pre_composition_functor _ _ _ *)
(*              (iter_functor1 optionHSET n) has_homsets_HSET has_homsets_HSET cats_LimsHSET *)
(*   end. *)

(* (* Old version: *) *)
(* (* Local Fixpoint precomp_option_iter (n : nat) : omega_cocont_functor HSET2 HSET2 := match n with *) *)
(* (*   | O => Id *) *)
(* (*   | S O => precomp_option *) *)
(* (*   | S n' => let G := omega_cocont_pre_composition_functor _ _ _ *) *)
(* (*                        (option_functor HSET CoproductsHSET TerminalHSET) has_homsets_HSET has_homsets_HSET cats_LimsHSET *) *)
(* (*                (* is this order correct???? *) *) *)
(* (*             in omega_cocont_functor_composite has_homsets_HSET2 G (iter_precomp_option n') *) *)
(* (*   end. *) *)

(* (* Definition SigToFunctor_helper2_Signature (n : nat) : Signature HSET has_homsets_HSET. *) *)
(* (* Proof. *) *)
(* (* mkpair. *) *)
(* (* - apply (precom n). *) *)
(* (* - mkpair; simpl. *) *)
(* (* + *) *)

(* Local Definition arity_to_functor : list nat -> omega_cocont_functor HSET2 HSET2. *)
(* Proof. *)
(* intro l. *)
(* generalize (map_list precomp_option_iter l). *)
(* apply foldr1_list. *)
(* - intros F G. *)
(*   apply (F * G). *)
(* - apply Id. *)
(* Defined. *)

(* Arguments arity_to_functor : simpl never. *)

(* Definition SigToFunctor : Sig -> omega_cocont_functor HSET2 HSET2. *)
(* Proof. *)
(* use foldr_list. *)
(* - intros l F. *)
(*   apply (arity_to_functor l + F). *)
(* - apply Id. *)
(* Defined. *)


(* New version *)
Eval cbn in (pr1 Id).

Definition precomp_option_iter (n : nat) : functor HSET2 HSET2 := match n with
  | O => functor_identity HSET2
  | S n => pre_composition_functor _ _ _ has_homsets_HSET _ (iter_functor1 optionHSET n)
  end.

Arguments iter_functor1 : simpl never.

Lemma is_omega_cocont_precomp_option_iter (n : nat) : is_omega_cocont (precomp_option_iter n).
Proof.
destruct n; simpl.
- apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- apply (is_omega_cocont_pre_composition_functor _ _ _ (iter_functor1 optionHSET n) _ _ cats_LimsHSET).
Qed.

Definition apa (n : nat) : Σ
   θ : θ_source_functor_data _ _ (precomp_option_iter n)
       ⟶ θ_target_functor_data _ _ (precomp_option_iter n),
       θ_Strength1_int θ × θ_Strength2_int θ.
Admitted.

Definition precomp_option_iter_Signature (n : nat) : Signature HSET has_homsets_HSET.
Proof.
mkpair.
- apply (precomp_option_iter n).
- apply apa.
Defined.

Lemma is_omega_cocont_precomp_iter_Signature (n : nat) : is_omega_cocont (precomp_option_iter_Signature n).
Proof.
apply is_omega_cocont_precomp_option_iter.
Qed.

(* Local Definition arity_to_functor : list nat -> omega_cocont_functor HSET2 HSET2. *)
(* Proof. *)
(* intro l. *)
(* generalize (map_list precomp_option_iter l). *)
(* apply foldr1_list. *)
(* - intros F G. *)
(*   apply (F * G). *)
(* - apply Id. *)
(* Defined. *)

(* Arguments arity_to_functor : simpl never. *)

Lemma is_omega_cocont_Product_of_Signatures (S1 S2 : Signature HSET has_homsets_HSET)
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2) :
  is_omega_cocont (Product_of_Signatures _ _ ProductsHSET S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_product_functor; try assumption.
- apply ProductsHSET2.
- apply has_exponentials_HSET2.
- apply has_homsets_HSET2.
- apply has_homsets_HSET2.
Qed.

(* Signature for the Id functor *)
Definition IdSignature : Signature HSET has_homsets_HSET.
Proof.
mkpair.
- apply Id.
- mkpair; simpl.
  + mkpair; simpl.
    * intro x.
      { mkpair.
        - intro y; simpl; apply idfun.
        - abstract (intros y y' f; apply idpath).
      }
    * abstract (intros y y' f; apply (nat_trans_eq has_homsets_HSET); intro z; apply idpath).
  + abstract (split;
               [ intros x; apply (nat_trans_eq has_homsets_HSET); intro z; apply idpath
               | intros x y z; apply (nat_trans_eq has_homsets_HSET); intro w; apply idpath]).
Defined.

Definition Arity_to_Signature : list nat -> Signature HSET has_homsets_HSET.
Proof.
intros xs.
generalize (map_list precomp_option_iter_Signature xs).
apply foldr1_list.
- apply (Product_of_Signatures _ _ ProductsHSET).
- apply IdSignature.
Defined.


(* Definition foldr1_list {A : UU} (f : A -> A -> A) (a : A) (l : list A) : A. *)
(* Proof. *)
(* destruct l as [n xs]. *)
(* destruct n. *)
(* - apply a. *)
(* - induction n as [|n F]. *)
(*   + apply (pr1 xs). *)
(*   + apply (f (pr1 xs) (F (pr2 xs))). *)
(* Defined. *)


Lemma is_omega_cocont_Arity_to_Signature (xs : list nat) : is_omega_cocont (Arity_to_Signature xs).
Proof.
destruct xs as [n xs].
destruct n.
- destruct xs; simpl; apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- induction n.
+
destruct xs as [m xs].
destruct xs; simpl.
apply is_omega_cocont_precomp_option_iter.
+
unfold Arity_to_Signature.
simpl in *.
destruct xs as [m xs].
generalize (IHn xs).
destruct xs.
apply is_omega_cocont_Product_of_Signatures.
apply is_omega_cocont_precomp_option_iter.
Defined.

Definition SigToSignature : Sig -> Signature HSET has_homsets_HSET.
Proof.
use foldr_list.
- intros l F.
  apply (Sum_of_Signatures _ _ CoproductsHSET (Arity_to_Signature l) F).
- apply IdSignature.
Defined.

Lemma is_omega_cocont_Sum_of_Signatures (S1 S2 : Signature HSET has_homsets_HSET)
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2) :
  is_omega_cocont (Sum_of_Signatures _ _ CoproductsHSET S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_coproduct_functor; try assumption.
- apply ProductsHSET2.
- apply has_homsets_HSET2.
- apply has_homsets_HSET2.
Qed.

Lemma is_omega_cocont_SigToSignature (s : Sig) : is_omega_cocont (SigToSignature s).
Proof.
destruct s as [n xs].
induction n.
destruct xs.
simpl.
apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
simpl.
destruct xs.
apply is_omega_cocont_Sum_of_Signatures.
apply is_omega_cocont_Arity_to_Signature.
apply IHn.
Qed.

Definition SigInitial (sig : Sig) :
  Initial (FunctorAlg (Id_H HSET has_homsets_HSET CoproductsHSET (SigToSignature sig))
                            (functor_category_has_homsets HSET HSET has_homsets_HSET)).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_coproduct_functor.
  + apply (Products_functor_precat _ _ ProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor; apply functor_category_has_homsets.
  + apply is_omega_cocont_SigToSignature.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Definition SigInitialHSS (sig : Sig) : Initial (hss_precategory CoproductsHSET (SigToSignature sig)).
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, cats_LimsHSET.
- apply SigInitial.
Defined.

Definition SigToMonad (sig : Sig) : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply CoproductsHSET.
- apply (SigToSignature sig).
- apply SigInitialHSS.
Defined.

End SigToMonad.


(* (* Test lambda calculus *) *)
(* Section test_lam. *)

(* Infix "::" := (cons_list nat). *)
(* Notation "[]" := (nil_list nat) (at level 0, format "[]"). *)

(* (* The signature of the lambda calculus: [[0,0],[1]] *) *)
(* Definition LamSig : Sig := cons_list (list nat) (0 :: 0 :: []) (cons_list (list nat) (1 :: []) (nil_list (list nat))). *)

(* Eval cbn in pr1 (SigToSignature LamSig). *)

(* Require Import UniMath.SubstitutionSystems.LamHSET. *)

(* Let Lam_S : Signature HSET has_homsets_HSET := *)
(*   Lam_Sig HSET has_homsets_HSET TerminalHSET CoproductsHSET ProductsHSET. *)

(* Check (pr1 Lam_S). *)
(* Goal (pr1 Lam_S = pr1 (SigToFunctor LamSig)). *)
(* simpl. *)
(* apply subtypeEquality. *)
(* intros x. *)
(* apply isaprop_is_functor. *)
(* apply (functor_category_has_homsets HSET HSET has_homsets_HSET). *)
(* simpl. *)
(* unfold App_H, square_functor. *)
(* unfold Abs_H. *)
(* apply maponpaths. *)
(* admit. *)
(* Abort. (* equal if we add Id *) *)

(* End test_lam. *)
