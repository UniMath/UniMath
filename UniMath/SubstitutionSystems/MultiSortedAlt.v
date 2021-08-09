(**

This file contains a fomalization of multisorted binding signatures:

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
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Slice.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Adjunctions.Examples.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted.

Local Open Scope cat.

(* These should be global *)
Arguments post_composition_functor {_ _ _} _ _ _.
Arguments pre_composition_functor {_ _ _} _ _ _.
Arguments Gθ_Signature {_ _ _ _ _ _} _ _.
Arguments Signature_Functor {_ _ _ _} _.
Arguments BinProduct_of_functors {_ _} _ _ _.
Arguments DL_comp {_ _ _} _ {_} _.
Arguments θ_from_δ_Signature {_ _ _} _.
Arguments BinProduct_of_Signatures {_ _ _ _} _ _ _.
Arguments Sum_of_Signatures _ {_ _ _ _} _ _.


(** * Definition of multisorted binding signatures *)
Section MBindingSig.

(* Interestingly we only need that Hsort is a 1-type *)
Variables (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).

(* Assumptions on C used to construct the functor *)
Variables (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).
(* Note that there is some redundancy in the assumptions *)

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)).

(** Define the discrete category of sorts *)
Let sort_cat : precategory := path_pregroupoid sort.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].
Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid f.

Let hsC : has_homsets C := homset_property C.
Let hs : has_homsets sortToC := homset_property sortToC.


(* Assumptions needed to prove ω-cocontinuity of the functor *)
Variables (expSortToCC : Exponentials (BinProducts_functor_precat sortToC C BP hsC))
          (HC : Colims_of_shape nat_graph C).
(* The expSortToCC assumption says that [sortToC,C] has exponentials. It
   could be reduced to exponentials in C, but we only have the case
   for C = Set formalized in

     CategoryTheory.categories.HSET.Structures.Exponentials_functor_HSET

*)


(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU :=
  ∑ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition mkMultiSortedSig {I : hSet}
  (ar : I → list (list sort × sort) × sort) : MultiSortedSig := (I,,ar).

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
Definition option_fun : sort → sortToC → sortToC.
Proof.
intros s A.
apply make_sortToC; intro t.
(* Instead of an if-then-else we use a coproduct over "s = t". This lets us
avoid assuming decidable equality for sort *)
exact (pr1 A t ⊕ CoproductObject (t = s) C (CC _ (Hsort t s) (λ _, 1))).
Defined.

Definition option_functor_data  (s : sort) : functor_data sortToC sortToC.
Proof.
use make_functor_data.
+ exact (option_fun s).
+ intros F G α.
  use make_nat_trans.
  * intro t; apply (BinCoproductOfArrows _ _ _ (pr1 α t) (identity _)).
  * abstract (now intros a b []; rewrite id_left, id_right).
Defined.

Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split.
+ intros F; apply (nat_trans_eq hsC); intro t; simpl.
  now apply pathsinv0, BinCoproductArrowUnique; rewrite id_left, id_right.
+ intros F G H αFG αGH; apply (nat_trans_eq hsC); intro t; simpl.
  apply pathsinv0; eapply pathscomp0; [apply precompWithBinCoproductArrow|].
  rewrite !id_left; apply BinCoproductArrowUnique.
  * now rewrite BinCoproductIn1Commutes, assoc.
  * now rewrite BinCoproductIn2Commutes, id_left.
Qed.

Local Definition option_functor (s : sort) : functor sortToC sortToC :=
  tpair _ _ (is_functor_option_functor s).

(** Sorted option functor for lists *)
Local Definition option_list (xs : list sort) : functor sortToC sortToC.
Proof.
(* This should be foldr1 in order to avoid composing with the
   identity functor in the base case *)
use (foldr1 (λ F G, F ∙ G) (functor_identity _) (map option_functor xs)).
Defined.


(** Define a functor

F^(l,t)(X) := projSortToC(t) ∘ X ∘ option_functor(l)

if l is nonempty and

F^(l,t)(X) := projSortToC(t) ∘ X

otherwise
 *)
Definition exp_functor (lt : list sort × sort) : functor [sortToC,sortToC] [sortToC,C].
Proof.
induction lt as [l t].
(* use list_ind to do a case on whether l is empty or not *)
use (list_ind _ _ _ l); clear l.
- exact (post_composition_functor _ _ (projSortToC t)).
- intros s l _; simpl.
  eapply functor_composite.
  + exact (pre_composition_functor hs hs (option_list (cons s l))).
  + exact (post_composition_functor _ hsC (projSortToC t)).
Defined.

(** This defines F^lts where lts is a list of (l,t). Outputs a product of
    functors if the list is nonempty and otherwise the constant functor. *)
Local Definition exp_functor_list (xs : list (list sort × sort)) :
  functor [sortToC,sortToC] [sortToC,C].
Proof.
(* If the list is empty we output the constant functor *)
set (T := constant_functor [sortToC,sortToC] [sortToC,C]
                           (constant_functor sortToC C TC)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
set (XS := map exp_functor xs).
(* This should be foldr1 in order to avoid composing with the
   constant functor in the base case *)
use (foldr1 (λ F G, BinProduct_of_functors _ F G) T XS).
apply BinProducts_functor_precat, BP.
Defined.

Local Definition hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  functor [sortToC,sortToC] [sortToC,sortToC] :=
    exp_functor_list (pr1 xst) ∙ post_composition_functor _ _ (hat_functor (pr2 xst)).

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

(** * Construction of the strength for the endofunctor on [SET/sort,SET/sort] derived from a
      multisorted signature *)
Section strength.

  (* TODO: finish this! *)
  Definition MultiSortedSigToSignature (M : MultiSortedSig) : Signature _ hs _ hs _ hs.
  Admitted.

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
  is_omega_cocont (@post_composition_functor sortToC _ _ hs hsC (projSortToC s)).
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
  is_omega_cocont (@post_composition_functor sortToC  _ _
       hsC hs (hat_functor s)).
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

End omega_cocont.


(** * Construction of a monad from a multisorted signature *)
Section monad.

Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat sort_cat _ BC hsC.
Let Id_H := Id_H sortToC hs BCsortToC.

Local Lemma has_homsets_SetSort2 : has_homsets [sortToC,sortToC].
Proof.
apply homset_property.
Defined.

Let FunctorAlg F := FunctorAlg F has_homsets_SetSort2.

(* ** Construction of initial algebra for a signature with strength on C^sort *)
Definition SignatureInitialAlgebraSetSort
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
+ admit. (* apply is_omega_cocont_MultiSortedSigToSignature. *)
Admitted.

(* The above HSS is initial *)
Definition MultiSortedSigToHSSisInitial (sig : MultiSortedSig) :
  isInitial _ (MultiSortedSigToHSS sig).
Admitted.
(* Proof. *)
(* now unfold MultiSortedSigToHSS, SignatureToHSS; destruct InitialHSS. *)
(* Qed. *)

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
