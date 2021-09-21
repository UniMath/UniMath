(**

This file contains a formalization of multisorted binding signatures:

- Definition of multisorted binding signatures ([MultiSortedSig])
- Construction of a functor from a multisorted binding signature
  ([MultiSortedSigToFunctor])
- Construction of signature with strength from a multisorted binding
  signature ([MultiSortedSigToSignature])
- Proof that the functor obtained from a multisorted binding signature
  is omega-cocontinuous ([is_omega_cocont_MultiSortedSigToFunctor])
- Construction of a monad on C^sort from a multisorted signature
  ([MultiSortedSigToMonad])
- Instantiation of MultiSortedSigToMonad for C = Set
  ([MultiSortedSigToMonadSet])

Written by: Anders Mörtberg, 2021. The formalization is an adaptation of
Multisorted.v

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
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Local Open Scope cat.

(* These should be global *)
Arguments Gθ_Signature {_ _ _ _ _ _} _ _.
Arguments Signature_Functor {_ _ _ _} _.
Arguments BinProduct_of_functors {_ _} _ _ _.
Arguments DL_comp {_ _ _} _ {_} _.
Arguments θ_from_δ_Signature {_ _ _} _.
Arguments BinProduct_of_Signatures {_ _ _ _} _ _ _.
Arguments Sum_of_Signatures _ {_ _ _ _} _ _.


(** * Definition of multisorted binding signatures *)
Section MBindingSig.

(* Interestingly we only need that [sort] is a 1-type *)
Variables (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).

(* Assumptions on [C] used to construct the functor *)
(* Note that there is some redundancy in the assumptions *)
Variables (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)

          (* TODO: check that these Products/Coproducts are OK *)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)).

(** Define the discrete category of sorts *)
Let sort_cat : precategory := path_pregroupoid sort.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].
Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid f.

Let hsC : has_homsets C := homset_property C.
Let hs : has_homsets sortToC := homset_property sortToC.
Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC hsC.

(* Assumptions needed to prove ω-cocontinuity of the functor *)
Variables (expSortToCC : Exponentials (BinProducts_functor_precat sortToC C BP hsC))
          (HC : Colims_of_shape nat_graph C).
(* The expSortToCC assumption says that [sortToC,C] has exponentials. It
   could be reduced to exponentials in C, but we only have the case
   for C = Set formalized in

     CategoryTheory.categories.HSET.Structures.Exponentials_functor_HSET

*)


(** Definition of multisorted signatures *)
Definition MultiSortedSig : UU :=
  ∑ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition mkMultiSortedSig {I : hSet}
  (ar : I → list (list sort × sort) × sort) : MultiSortedSig := (I,,ar).

(** Sum of multisorted binding signatures *)
Definition SumMultiSortedSig : MultiSortedSig → MultiSortedSig → MultiSortedSig.
Proof.
intros s1 s2.
use tpair.
- apply (setcoprod (ops s1) (ops s2)).
- induction 1 as [i|i].
  + apply (arity s1 i).
  + apply (arity s2 i).
Defined.

(** * Construction of an endofunctor on [C^sort,C^sort] from a multisorted signature *)
Section functor.

(** Given a sort s this applies the sortToC to s and returns C *)
Definition projSortToC (s : sort) : functor sortToC C.
Proof.
use tpair.
+ use tpair.
  - intro f; apply (pr1 f s).
  - simpl; intros a b f; apply (f s).
+ abstract (split; intros f *; apply idpath).
Defined.

(* The left adjoint to projSortToC *)
Definition hat_functor (t : sort) : functor C sortToC.
Proof.
use tpair.
+ use tpair.
  - intros A.
    use make_sortToC; intros s.
    use (CoproductObject (t = s) C (CC _ (Hsort t s) (λ _, A))).
  - intros a b f.
    apply (nat_trans_functor_path_pregroupoid hsC); intros s.
    apply CoproductOfArrows; intros p; apply f.
+ split.
  - abstract (intros x; apply (nat_trans_eq hsC); intros s;
    apply pathsinv0, CoproductArrowUnique; intros p;
    now rewrite id_left, id_right).
  - abstract (intros x y z f g; apply (nat_trans_eq hsC); intros s;
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
  BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ BCsortToC hs
                                                  (constant_functor _ _ option_fun_summand)
                                                  (functor_identity sortToC)).


Local Definition None_sorted_option_functor : constant_functor _ _ option_fun_summand ⟹ sorted_option_functor :=
  BinCoproductIn1 _ (BinCoproducts_functor_precat _ _ BCsortToC hs
                                                  (constant_functor _ _ option_fun_summand)
                                                  (functor_identity sortToC)).

End Sorted_Option_Functor.


(** Sorted option functor for lists *)
Definition option_list (xs : list sort) : [sortToC,sortToC].
Proof.
(* This should be foldr1 in order to avoid composing with the
   identity functor in the base case *)
use (foldr1 (λ F G, F ∙ G) (functor_identity _) (map sorted_option_functor xs)).
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
set (XS := map exp_functor xs).
(* This should be foldr1 in order to avoid composing with the
   constant functor in the base case *)
use (foldr1 (λ F G, BinProduct_of_functors _ F G) T XS).
apply BinProducts_functor_precat, BP.
Defined.

Definition hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  functor [sortToC,sortToC] [sortToC,sortToC] :=
    exp_functor_list (pr1 xst) ∙ post_comp_functor (hat_functor (pr2 xst)).

(** The function from multisorted signatures to functors *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig) :
  functor [sortToC,sortToC] [sortToC,sortToC].
Proof.
use (coproduct_of_functors (ops M)).
+ apply Coproducts_functor_precat, Coproducts_functor_precat, CC, setproperty.
+ intros op.
  exact (hat_exp_functor_list (arity M op)).
Defined.

End functor.

(** * Construction of the strength for the endofunctor on [C^sort,C^sort] derived from a
      multisorted signature *)
Section strength.

(* The distributive law for sorted_option_functor *)
Definition DL_sorted_option_functor (s : sort) :
  DistributiveLaw sortToC hs (sorted_option_functor s) :=
    genoption_DistributiveLaw sortToC hs (option_fun_summand s) BCsortToC.

(* The DL for option_list *)
Definition DL_option_list (xs : list sort) :
  DistributiveLaw _ hs (option_list xs).
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
  Signature _ hs _ hsC _ hs.
Proof.
exists (exp_functor lt).
induction lt as [l t].
induction l as [[|n] xs].
+ induction xs.
  exact (pr2 (Gθ_Signature _ _ (IdSignature _ _ _ _) (projSortToC t))).
+ induction n as [|n IH].
  * induction xs as [m []].
    set (Sig_option_list := θ_from_δ_Signature (DL_option_list (cons m (0,,tt)))).
    exact (pr2 (Gθ_Signature _ _ Sig_option_list (projSortToC t))).
  * induction xs as [m xs].
    set (Sig_option_list := θ_from_δ_Signature (DL_option_list (cons m (S n,,xs)))).
    exact (pr2 (Gθ_Signature _ _ Sig_option_list (projSortToC t))).
Defined.

Local Lemma functor_in_Sig_exp_functor_ok (lt : list sort × sort) :
  Signature_Functor _ _ (Sig_exp_functor lt) = exp_functor lt.
Proof.
apply idpath.
Qed.

(* The signature for exp_functor_list *)
Definition Sig_exp_functor_list (xs : list (list sort × sort)) :
  Signature _ hs _ hsC _ hs.
Proof.
exists (exp_functor_list xs).
induction xs as [[|n] xs].
- induction xs.
  exact (pr2 (ConstConstSignature _ _ _ _)).
- induction n as [|n IH].
  + induction xs as [m []].
    exact (pr2 (Sig_exp_functor m)).
  + induction xs as [m [k xs]].
    exact (pr2 (BinProduct_of_Signatures _ _ _ (Sig_exp_functor _) (tpair _ _ (IH (k,,xs))))).
Defined.

Local Lemma functor_in_Sig_exp_functor_list_ok (xs : list (list sort × sort)) :
  Signature_Functor _ _ (Sig_exp_functor_list xs) = exp_functor_list xs.
Proof.
apply idpath.
Qed.

(* the signature for hat_exp_functor_list *)
Definition Sig_hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  Signature _ hs _ hs _ hs.
Proof.
apply (Gθ_Signature _ _ (Sig_exp_functor_list (pr1 xst)) (hat_functor (pr2 xst))).
Defined.

Local Lemma functor_in_Sig_hat_exp_functor_list_ok (xst : list (list sort × sort) × sort) :
  Signature_Functor _ _ (Sig_hat_exp_functor_list xst) = hat_exp_functor_list xst.
Proof.
apply idpath.
Qed.

(* The signature for MultiSortedSigToFunctor *)
Definition MultiSortedSigToSignature (M : MultiSortedSig) : Signature _ hs _ hs _ hs.
Proof.
set (Hyps := λ (op : ops M), Sig_hat_exp_functor_list (arity M op)).
use (Sum_of_Signatures (ops M) _ _ _ Hyps).
apply Coproducts_functor_precat, CC, setproperty.
Defined.

Local Lemma functor_in_MultiSortedSigToSignature_ok (M : MultiSortedSig) :
  Signature_Functor _ _ (MultiSortedSigToSignature M) = MultiSortedSigToFunctor M.
Proof.
apply idpath.
Qed.

End strength.


(** * Proof that the functor obtained from a multisorted signature is omega-cocontinuous *)
Section omega_cocont.

(* Direct definition of the right adjoint to projSortToC *)
Local Definition projSortToC_rad (t : sort) : functor C sortToC.
Proof.
use tpair.
+ use tpair.
  - intros A.
    use make_sortToC; intros s.
    exact (ProductObject (t = s) C (PC _ (λ _, A))).
  - intros a b f.
    apply (nat_trans_functor_path_pregroupoid hsC); intros s.
    apply ProductOfArrows; intros p; apply f.
+ split.
  - abstract (intros x; apply (nat_trans_eq hsC); intros s;
    apply pathsinv0, ProductArrowUnique; intros p;
    now rewrite id_left, id_right).
  - abstract(intros x y z f g; apply (nat_trans_eq hsC); intros s; cbn;
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
  + abstract (intros A B F; apply (nat_trans_eq hsC); intros t; cbn;
    rewrite precompWithProductArrow, postcompWithProductArrow;
    apply ProductArrowUnique; intros []; cbn;
    now rewrite (ProductPrCommutes _ _ _ (PC _ (λ _, pr1 B s))), id_left, id_right).
- use make_nat_trans.
  + intros A.
    exact (ProductPr _ _ (PC _ (λ _, A)) (idpath _)).
  + abstract (now intros a b f; cbn; rewrite (ProductOfArrowsPr _ _ (PC _ (λ _, b)))).
- use make_form_adjunction.
  + intros A; cbn.
    now rewrite (ProductPrCommutes _ _ _ (PC _ (λ _, pr1 A s))).
  + intros c; apply (nat_trans_eq hsC); intros t; cbn.
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
induction a as [xs t].
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_post_comp_projSortToC.
- induction n as [|n].
  + induction xs as [m []].
    use is_omega_cocont_functor_composite.
    * apply functor_category_has_homsets.
    * now apply is_omega_cocont_pre_composition_functor, ColimsFunctorCategory_of_shape.
    * apply is_omega_cocont_post_comp_projSortToC.
  + induction xs as [m k]; simpl.
    use (@is_omega_cocont_functor_composite _ [sortToC,_,_]).
    * apply (functor_category_has_homsets sortToC C hsC).
    * apply (is_omega_cocont_pre_composition_functor (option_list (cons m (S n,,k))) hs hs).
      now use ColimsFunctorCategory_of_shape.
    * apply is_omega_cocont_post_comp_projSortToC.
Defined.

Local Lemma is_omega_cocont_exp_functor_list (xs : list (list sort × sort)) :
  is_omega_cocont (exp_functor_list xs).
Proof.
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_constant_functor, functor_category_has_homsets.
- induction n as [|n IHn].
  + induction xs as [m []].
    apply is_omega_cocont_exp_functor.
  + induction xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors; try apply homset_property.
    * apply BinProducts_functor_precat, BinProducts_functor_precat, BP.
    * apply is_omega_cocont_constprod_functor1; try apply functor_category_has_homsets.
      apply expSortToCC.
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
    apply (nat_trans_eq hsC); intros t; cbn;
    rewrite precompWithCoproductArrow, postcompWithCoproductArrow;
    apply CoproductArrowUnique; intros []; cbn;
    now rewrite id_left, (CoproductInCommutes _ _ _ (CC _ _ (λ _, pr1 A s))), id_right).
- use make_form_adjunction.
  + intros c; apply (nat_trans_eq hsC); intros t; cbn.
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
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_exp_functor_list.
+ apply is_omega_cocont_post_comp_hat_functor.
Defined.

(** The functor obtained from a multisorted binding signature is omega-cocontinuous *)
Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig) :
  is_omega_cocont (MultiSortedSigToFunctor M).
Proof.
apply is_omega_cocont_coproduct_of_functors; try apply homset_property.
intros op; apply is_omega_cocont_hat_exp_functor_list.
Defined.

Lemma is_omega_cocont_MultiSortedSigToSignature (M : MultiSortedSig) :
  is_omega_cocont (MultiSortedSigToSignature M).
Proof.
apply is_omega_cocont_MultiSortedSigToFunctor.
Defined.

End omega_cocont.


(** * Construction of a monad from a multisorted signature *)
Section monad.

Let Id_H := Id_H sortToC hs BCsortToC.

Local Lemma has_homsets_SetSort2 : has_homsets [sortToC,sortToC].
Proof.
apply homset_property.
Defined.

Let FunctorAlg F := FunctorAlg F has_homsets_SetSort2.

(* ** Construction of initial algebra for a signature with strength on C^sort *)
Definition SignatureInitialAlgebra
  (H : Signature _ hs _ hs _ hs) (Hs : is_omega_cocont H) :
  Initial (FunctorAlg (Id_H H)).
Proof.
use colimAlgInitial.
- apply Initial_functor_precat, Initial_functor_precat, IC.
- apply (is_omega_cocont_Id_H), Hs.
- apply ColimsFunctorCategory_of_shape, ColimsFunctorCategory_of_shape, HC.
Defined.

Let HSS := @hss_precategory _ hs BCsortToC.

(* ** Multisorted signature to a HSS *)
Definition MultiSortedSigToHSS (sig : MultiSortedSig) :
  HSS (MultiSortedSigToSignature sig).
Proof.
apply SignatureToHSS.
+ apply Initial_functor_precat, IC.
+ apply ColimsFunctorCategory_of_shape, HC.
+ apply is_omega_cocont_MultiSortedSigToSignature.
Defined.

(* The above HSS is initial *)
Definition MultiSortedSigToHSSisInitial (sig : MultiSortedSig) :
  isInitial _ (MultiSortedSigToHSS sig).
Proof.
now unfold MultiSortedSigToHSS, SignatureToHSS; destruct InitialHSS.
Qed.

(** ** Function from multisorted binding signatures to monads *)
Definition MultiSortedSigToMonad (sig : MultiSortedSig) : Monad sortToC.
Proof.
use Monad_from_hss.
- apply hs.
- apply BCsortToC.
- apply (MultiSortedSigToSignature sig).
- apply MultiSortedSigToHSS.
Defined.

End monad.
End MBindingSig.

Section MBindingSigMonadHSET.

(* Assume a set of sorts *)
Variable (sort : hSet).

Let sortToSet : category := [path_pregroupoid sort,SET].
Let hs : has_homsets sortToSet := homset_property sortToSet.

Definition projSortToSet : sort → functor sortToSet SET :=
  projSortToC sort SET.

Definition hat_functorSet : sort → SET ⟶ sortToSet :=
  hat_functor sort (isofhlevelssnset 1 _ (setproperty sort)) SET CoproductsHSET.

Definition sorted_option_functorSet : sort → sortToSet ⟶ sortToSet :=
  sorted_option_functor _ (isofhlevelssnset 1 _ (setproperty sort)) SET
                        TerminalHSET BinCoproductsHSET CoproductsHSET.

Definition MultiSortedSigToSignatureSet : MultiSortedSig sort → Signature _ hs _ hs _ hs.
Proof.
use MultiSortedSigToSignature.
- apply isofhlevelssnset, setproperty.
- apply TerminalHSET.
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply CoproductsHSET.
Defined.

Definition MultiSortedSigToMonadSet (ms : MultiSortedSig sort) :
  Monad sortToSet.
Proof.
use MultiSortedSigToMonad.
- apply isofhlevelssnset, setproperty.
- apply TerminalHSET.
- apply InitialHSET.
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply ProductsHSET.
- apply CoproductsHSET.
- apply Exponentials_functor_HSET, functor_category_has_homsets.
- apply ColimsHSET_of_shape.
- apply ms.
Defined.

End MBindingSigMonadHSET.
