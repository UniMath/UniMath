(**

This file contains a formalization of multisorted binding signatures:

- Definition of multisorted binding signatures ([MultiSortedSig])
- Construction of a functor from a multisorted binding signature
  ([MultiSortedSigToFunctor])
- Construction of signature with strength from a multisorted binding
  signature ([MultiSortedSigToSignature])
- Proof that the functor obtained from a multisorted binding signature
  is omega-cocontinuous ([is_omega_cocont_MultiSortedSigToFunctor])

The construction of a monad on C^sort from a multisorted signature and the
instantiation of MultiSortedSigToMonad for C = Set are now found in
[UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt].


Written by: Anders Mörtberg, 2021. The formalization is an adaptation of
Multisorted.

some adaptions in preparation of actegorical approach done in 2023 by Ralph Matthes

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.

Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require UniMath.SubstitutionSystems.SortIndexing.

Local Open Scope cat.

(* These should be global *)
Arguments Gθ_Signature {_ _ _ _} _ _.
Arguments Signature_Functor {_ _ _} _.
Arguments BinProduct_of_functors {_ _} _ _ _.
Arguments DL_comp {_ _} _ {_} _.
Arguments θ_from_δ_Signature {_ _} _.
Arguments BinProduct_of_Signatures {_ _ _} _ _ _.
Arguments Sum_of_Signatures _ {_ _ _} _ _.


(** * Definition of multisorted binding signatures *)
Section MBindingSig.

(* Interestingly we only need that [sort] is a 1-type *)
Context (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).

(* Assumptions on [C] used to construct the functor *)
(* Note that there is some redundancy in the assumptions *)
Context (TC : Terminal C) (IC : Initial C)
        (BP : BinProducts C) (BC : BinCoproducts C)
        (* (PC : forall (I : UU), Products I C) *) (eqsetPC : forall (s s' : sort), Products (s=s') C)
        (CC : forall (I : UU), isaset I → Coproducts I C).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject (BC a b)).

(** Define the category of sorts *)
Let sort_cat : category := path_pregroupoid sort Hsort.

Goal sort_cat = SortIndexing.sort_cat sort Hsort.
Proof.
  apply idpath.
Qed.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].

Goal sortToC = SortIndexing.sortToC sort Hsort C.
Proof.
  apply idpath.
Qed.

Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Goal make_sortToC = SortIndexing.make_sortToC sort Hsort C.
Proof.
  apply idpath.
Qed.

Let make_sortToC_mor (ξ ξ' : sortToC) (fam : ∏ s: sort, pr1 ξ s --> pr1 ξ' s) : sortToC⟦ξ,ξ'⟧
    := nat_trans_functor_path_pregroupoid fam.

Goal make_sortToC_mor = SortIndexing.make_sortToC_mor sort Hsort C.
Proof.
  apply idpath.
Qed.

Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.

Goal BCsortToC = SortIndexing.BCsortToC sort Hsort _ BC.
Proof.
  apply idpath.
Qed. (* slow *)

Let BPsortToCC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

Goal BPsortToCC = SortIndexing.BPsortToCC sort Hsort _ BP.
Proof.
  apply idpath.
Qed. (* slow *)

(* Assumptions needed to prove ω-cocontinuity of the functor *)
Context (EsortToCC : Exponentials BPsortToCC)
        (HC : Colims_of_shape nat_graph C).
(* The EsortToCC assumption says that [sortToC,C] has exponentials. It
   could be reduced to exponentials in C, but we only have the case
   for C = Set formalized in

     CategoryTheory.Categories.HSET.Structures.Exponentials_functor_HSET

*)

Definition CoproductsMultiSortedSig_base (M : MultiSortedSig sort) : Coproducts (ops _ M) sortToC.
Proof.
  apply Coproducts_functor_precat, CC, setproperty.
Defined.

Goal CoproductsMultiSortedSig_base = fun M => SortIndexing.CCsortToC sort Hsort C CC _ (setproperty (ops sort M)).
Proof.
  apply idpath.
Qed. (* slow *)

Definition CoproductsMultiSortedSig (M : MultiSortedSig sort) : Coproducts (ops _ M) [sortToC, sortToC].
Proof.
  apply Coproducts_functor_precat, CoproductsMultiSortedSig_base.
Defined.

Goal CoproductsMultiSortedSig = fun M => SortIndexing.CCsortToC2 sort Hsort C CC _ (setproperty (ops sort M)).
Proof.
  apply idpath.
Qed. (* slow *)


(** * Construction of an endofunctor on [C^sort,C^sort] from a multisorted signature *)
Section functor.

(** Given a sort s this applies the sortToC to s and returns C *)
Definition projSortToC (s : sort) : functor sortToC C.
Proof.
use make_functor.
+ use make_functor_data.
  - intro ξ; apply (pr1 ξ s).
  - simpl; intros a b ξ; apply (ξ s).
+ abstract (split; intros ξ *; apply idpath).
Defined.

(** not needed here - illustration that also the sort can vary *)
Definition projSortToCvariable (f: sort -> sort) : functor sortToC sortToC.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro ξ.
      apply make_sortToC.
      intro s.
      exact (pr1 ξ (f s)).
    + intros ξ ξ' h.
      apply make_sortToC_mor.
      intro s.
      exact (pr1 h (f s)).
  - abstract (split; red; intros; apply nat_trans_eq; try (apply C);
      intro t; apply idpath).
Defined.

(* The left adjoint to projSortToC *)
Definition hat_functor (t : sort) : functor C sortToC.
Proof.
use make_functor.
+ use make_functor_data.
  - intros A.
    use make_sortToC; intros s.
    use (CoproductObject (t = s) C (CC _ (Hsort t s) (λ _, A))).
  - intros a b f.
    apply (nat_trans_functor_path_pregroupoid); intros s.
    apply CoproductOfArrows; intros p; apply f.
+ split.
  - abstract (intros x; apply nat_trans_eq_alt; intros s;
    apply pathsinv0, CoproductArrowUnique; intros p;
    now rewrite id_left, id_right).
  - abstract (intros x y z f g; apply nat_trans_eq_alt; intros s;
    apply pathsinv0, CoproductArrowUnique; intros p; cbn;
    now rewrite assoc, (CoproductOfArrowsIn _ _ (CC _ (Hsort t s) (λ _, x))),
            <- !assoc, (CoproductOfArrowsIn _ _ (CC _ (Hsort t s) (λ _, y)))).
Defined.


(* The option functor (without decidable equality) *)
Section Sorted_Option_Functor.

Context (s : sort).

Definition option_fun_summand : sortToC.
Proof.
apply make_sortToC; intro t.
(* Instead of an if-then-else we use a coproduct over "s = t". This lets us
avoid assuming decidable equality for sort *)
exact (CoproductObject (t = s) C (CC _ (Hsort t s) (λ _, 1))).
Defined.

Definition sorted_option_functor : functor sortToC sortToC :=
  constcoprod_functor1 BCsortToC option_fun_summand.

(** the following two definitions are currently not used *)

Local Definition Some_sorted_option_functor : functor_identity sortToC ⟹ sorted_option_functor :=
  BinCoproductIn2 (BinCoproducts_functor_precat _ _ BCsortToC
                                                  (constant_functor _ _ option_fun_summand)
                                                  (functor_identity sortToC)).


Local Definition None_sorted_option_functor : constant_functor _ _ option_fun_summand ⟹ sorted_option_functor :=
  BinCoproductIn1 (BinCoproducts_functor_precat _ _ BCsortToC
                                                  (constant_functor _ _ option_fun_summand)
                                                  (functor_identity sortToC)).

End Sorted_Option_Functor.


(** Sorted option functor for lists *)
Definition option_list (xs : list sort) : [sortToC,sortToC].
Proof.
(* This should be [foldr1] or [foldr1_map] in order to avoid composing with the
   identity functor on the right in the base case *)
use (foldr1_map (λ F G, F ∙ G) (functor_identity _) sorted_option_functor xs).
Defined.


(** Define a functor

F^(l,t)(X) := projSortToC(t) ∘ X ∘ sorted_option_functor(l)

if l is nonempty and

F^(l,t)(X) := projSortToC(t) ∘ X

otherwise
 *)
Definition exp_functor (lt : list sort × sort) : functor [sortToC,sortToC] [sortToC,C].
Proof.
induction lt as [l t].
(* use list_ind to do a case on whether l is empty or not *)
use (list_ind _ _ _ l); clear l.
- exact (post_comp_functor (projSortToC t)).
- intros s l _.
  exact (pre_comp_functor (option_list (cons s l)) ∙ post_comp_functor (projSortToC t)).
Defined.

(** This defines F^lts where lts is a list of (l,t). Outputs a product of
    functors if the list is nonempty and otherwise the constant functor. *)
Definition exp_functor_list (xs : list (list sort × sort)) :
  functor [sortToC,sortToC] [sortToC,C].
Proof.
(* If the list is empty we output the constant functor *)
set (T := constant_functor [sortToC,sortToC] [sortToC,C]
                           (constant_functor sortToC C TC)).
(* This should be [foldr1] or [foldr1_map] in order to avoid composing with the
   constant functor in the base case *)
exact (foldr1_map (λ F G, BinProduct_of_functors BPsortToCC F G) T exp_functor xs).
Defined.

Definition hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  functor [sortToC,sortToC] [sortToC,sortToC] :=
    exp_functor_list (pr1 xst) ∙ post_comp_functor (hat_functor (pr2 xst)).

(** The function from multisorted signatures to functors *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig sort) :
  functor [sortToC,sortToC] [sortToC,sortToC].
Proof.
  use (coproduct_of_functors (ops _ M) _ _ (CoproductsMultiSortedSig M)).
  intros op.
  exact (hat_exp_functor_list (arity _ M op)).
Defined.

End functor.

(** * Construction of the strength for the endofunctor on [C^sort,C^sort]
      derived from a multisorted signature *)
Section strength.

(* The distributive law for sorted_option_functor *)
Definition DL_sorted_option_functor (s : sort) :
  DistributiveLaw sortToC (sorted_option_functor s) :=
    genoption_DistributiveLaw sortToC (option_fun_summand s) BCsortToC.

(* The DL for option_list *)
Definition DL_option_list (xs : list sort) : DistributiveLaw _ (option_list xs).
Proof.
induction xs as [[|n] xs].
+ induction xs.
  apply DL_id.
+ induction n as [|n IH].
  * induction xs as [m []].
    apply DL_sorted_option_functor.
  * induction xs as [m [k xs]].
    apply (DL_comp (DL_sorted_option_functor m) (IH (k,,xs))).
Defined.

(* The signature for exp_functor *)
Definition Sig_exp_functor (lt : list sort × sort) :
  Signature sortToC C sortToC.
Proof.
exists (exp_functor lt).
induction lt as [l t]; revert l.
use list_ind.
+ exact (pr2 (Gθ_Signature (IdSignature _ _) (projSortToC t))).
+ intros x xs H; simpl.
  set (Sig_option_list := θ_from_δ_Signature (DL_option_list (cons x xs))).
  apply (pr2 (Gθ_Signature Sig_option_list (projSortToC t))).
Defined.

Local Lemma functor_in_Sig_exp_functor_ok (lt : list sort × sort) :
  Signature_Functor (Sig_exp_functor lt) = exp_functor lt.
Proof.
apply idpath.
Qed.

(* The signature for exp_functor_list *)
Definition Sig_exp_functor_list (xs : list (list sort × sort)) :
  Signature sortToC C sortToC.
Proof.
exists (exp_functor_list xs).
induction xs as [[|n] xs].
- induction xs.
  exact (pr2 (ConstConstSignature _ _ _ _)).
- induction n as [|n IH].
  + induction xs as [m []].
    exact (pr2 (Sig_exp_functor m)).
  + induction xs as [m [k xs]].
    exact (pr2 (BinProduct_of_Signatures _ (Sig_exp_functor _) (tpair _ _ (IH (k,,xs))))).
Defined.

Local Lemma functor_in_Sig_exp_functor_list_ok (xs : list (list sort × sort)) :
  Signature_Functor (Sig_exp_functor_list xs) = exp_functor_list xs.
Proof.
apply idpath.
Qed.

(* the signature for hat_exp_functor_list *)
Definition Sig_hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  Signature sortToC sortToC sortToC.
Proof.
apply (Gθ_Signature (Sig_exp_functor_list (pr1 xst)) (hat_functor (pr2 xst))).
Defined.

Local Lemma functor_in_Sig_hat_exp_functor_list_ok (xst : list (list sort × sort) × sort) :
  Signature_Functor (Sig_hat_exp_functor_list xst) = hat_exp_functor_list xst.
Proof.
apply idpath.
Qed.

(* The signature for MultiSortedSigToFunctor *)
Definition MultiSortedSigToSignature (M : MultiSortedSig sort) : Signature sortToC sortToC sortToC.
Proof.
set (Hyps := λ (op : ops _ M), Sig_hat_exp_functor_list (arity _ M op)).
apply (Sum_of_Signatures (ops _ M) (CoproductsMultiSortedSig_base M) Hyps).
Defined.

Local Lemma functor_in_MultiSortedSigToSignature_ok (M : MultiSortedSig sort) :
  Signature_Functor (MultiSortedSigToSignature M) = MultiSortedSigToFunctor M.
Proof.
apply idpath.
Qed.

End strength.


(** * Proof that the functor obtained from a multisorted signature is omega-cocontinuous *)
Section omega_cocont.

(* Direct definition of the right adjoint to projSortToC *)
Local Definition projSortToC_rad (t : sort) : functor C sortToC.
Proof.
use make_functor.
+ use make_functor_data.
  - intros A.
    use make_sortToC; intros s.
    exact (ProductObject (t = s) C (eqsetPC _ _ (λ _, A))).
  - intros a b f.
    apply (nat_trans_functor_path_pregroupoid); intros s.
    apply ProductOfArrows; intros p; apply f.
+ split.
  - abstract (intros x; apply nat_trans_eq_alt; intros s;
    apply pathsinv0, ProductArrowUnique; intros p;
    now rewrite id_left, id_right).
  - abstract(intros x y z f g; apply nat_trans_eq_alt; intros s; cbn;
    now rewrite ProductOfArrows_comp).
Defined.

Local Lemma is_left_adjoint_projSortToC (s : sort) : is_left_adjoint (projSortToC s).
Proof.
exists (projSortToC_rad s).
use make_are_adjoints.
- use make_nat_trans.
  + intros A.
    use make_nat_trans.
    * intros t; apply ProductArrow; intros p; induction p; apply identity.
    * abstract (now intros a b []; rewrite id_right, (functor_id A), id_left).
  + abstract (intros A B F; apply nat_trans_eq_alt; intros t; cbn;
    rewrite precompWithProductArrow, postcompWithProductArrow;
    apply ProductArrowUnique; intros []; cbn;
    now rewrite (ProductPrCommutes _ _ _ (eqsetPC _ _ (λ _, pr1 B s))), id_left, id_right).
- use make_nat_trans.
  + intros A.
    exact (ProductPr _ _ (eqsetPC _  _ (λ _, A)) (idpath _)).
  + abstract (now intros a b f; cbn; rewrite (ProductOfArrowsPr _ _ (eqsetPC _  _ (λ _, b)))).
- use make_form_adjunction.
  + intros A; cbn.
    now rewrite (ProductPrCommutes _ _ _ (eqsetPC _  _ (λ _, pr1 A s))).
  + intros c; apply nat_trans_eq_alt; intros t; cbn.
    rewrite postcompWithProductArrow.
    apply pathsinv0, ProductArrowUnique; intros [].
    now rewrite !id_left.
Qed.

Local Lemma is_omega_cocont_post_comp_projSortToC (s : sort) :
  is_omega_cocont (post_comp_functor (A := sortToC) (projSortToC s)).
Proof.
apply is_omega_cocont_post_composition_functor.
apply is_left_adjoint_projSortToC.
Defined.

Local Lemma is_omega_cocont_exp_functor (a : list sort × sort) :
  is_omega_cocont (exp_functor a).
Proof.
induction a as [xs t]; revert xs.
use list_ind.
- apply is_omega_cocont_post_comp_projSortToC.
- intros x xs H.
  apply is_omega_cocont_functor_composite.
  + apply (is_omega_cocont_pre_composition_functor (option_list _)).
    apply (ColimsFunctorCategory_of_shape nat_graph sort_cat _ HC).
  + apply is_omega_cocont_post_comp_projSortToC.
Defined.

Local Lemma is_omega_cocont_exp_functor_list (xs : list (list sort × sort)) :
  is_omega_cocont (exp_functor_list xs).
Proof.
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_constant_functor.
- induction n as [|n IHn].
  + induction xs as [m []].
    apply is_omega_cocont_exp_functor.
  + induction xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors.
    * apply BinProducts_functor_precat, BinProducts_functor_precat, BP.
    * apply is_omega_cocont_constprod_functor1.
      apply EsortToCC.
    * apply is_omega_cocont_exp_functor.
    * apply (IHn (k,,xs)).
Defined.

(* The hat_functor is left adjoint to projSortToC *)
Local Lemma is_left_adjoint_hat (s : sort) : is_left_adjoint (hat_functor s).
Proof.
exists (projSortToC s).
use make_are_adjoints.
- use make_nat_trans.
  + intros A.
    exact (CoproductIn _ _ (CC (s = s) _ (λ _, A)) (idpath _)).
  + abstract (now intros A B f; cbn; rewrite (CoproductOfArrowsIn _ _ (CC _ _ (λ _, A)))).
- use make_nat_trans.
  + intros A.
    use make_nat_trans.
    * intros t; apply CoproductArrow; intros p.
      exact (transportf (λ z, C ⟦ pr1 A s , z ⟧) (maponpaths (pr1 A) p) (identity _)).
    * abstract (intros a b []; now rewrite id_left, (functor_id A), id_right).
  + abstract (intros A B F;
    apply nat_trans_eq_alt; intros t; cbn;
    rewrite precompWithCoproductArrow, postcompWithCoproductArrow;
    apply CoproductArrowUnique; intros []; cbn;
    now rewrite id_left, (CoproductInCommutes _ _ _ (CC _ _ (λ _, pr1 A s))), id_right).
- use make_form_adjunction.
  + intros c; apply nat_trans_eq_alt; intros t; cbn.
    rewrite precompWithCoproductArrow.
    apply pathsinv0, CoproductArrowUnique; intros [].
    now rewrite !id_right.
  + intros A; cbn.
    now rewrite (CoproductInCommutes _ _ _ (CC _ _ (λ _, pr1 A s))).
Qed.

Local Lemma is_omega_cocont_post_comp_hat_functor (s : sort) :
  is_omega_cocont (post_comp_functor (A := sortToC) (hat_functor s)).
Proof.
apply is_omega_cocont_post_composition_functor, is_left_adjoint_hat.
Defined.

Local Lemma is_omega_cocont_hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  is_omega_cocont (hat_exp_functor_list xst).
Proof.
  apply is_omega_cocont_functor_composite.
  + apply is_omega_cocont_exp_functor_list.
  + apply is_omega_cocont_post_comp_hat_functor.
Defined.

(** The functor obtained from a multisorted binding signature is omega-cocontinuous *)
Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig sort) :
  is_omega_cocont (MultiSortedSigToFunctor M).
Proof.
  apply is_omega_cocont_coproduct_of_functors.
  intros op; apply is_omega_cocont_hat_exp_functor_list.
Defined.

Lemma is_omega_cocont_MultiSortedSigToSignature (M : MultiSortedSig sort) :
  is_omega_cocont (MultiSortedSigToSignature M).
Proof.
  apply is_omega_cocont_MultiSortedSigToFunctor.
Defined.

End omega_cocont.

End MBindingSig.
