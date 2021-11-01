(**

This file contains a fomalization of multisorted binding signatures:

- Definition of multisorted binding signatures ([MultiSortedSig])
- Construction of a functor from a multisorted binding signature
  ([MultiSortedSigToFunctor])
- Construction of signature with strength from a multisorted binding
  signature ([MultiSortedSigToSignature])
- Proof that the functor obtained from a multisorted binding signature
  is omega-cocontinuous ([is_omega_cocont_MultiSortedSigToFunctor])
- Construction of a monad on Set/sort from a multisorted signature
  ([MultiSortedSigToMonad])


Written by: Anders Mörtberg, 2016. The formalization follows a note
written by Benedikt Ahrens and Ralph Matthes, and is also inspired by
discussions with them and Vladimir Voevodsky.

Strength calculation added by Ralph Matthes, 2017.

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

Local Notation "C / X" := (slicecat_ob C X).
Local Notation "C / X" := (slice_precat_data C X).
Local Notation "C / X" := (slice_cat C X).
Local Notation "C / X ⟦ a , b ⟧" := (slicecat_mor C X a b) (at level 50, format "C / X ⟦ a , b ⟧").

(* These should be global *)
Arguments post_composition_functor {_ _ _} _.
Arguments pre_composition_functor {_ _ _} _.
Arguments Gθ_Signature {_ _ _ _} _ _.
Arguments Signature_Functor {_ _ _} _.
Arguments BinProduct_of_functors {_ _} _ _ _.
Arguments DL_comp {_ _} _ {_} _.
Arguments θ_from_δ_Signature {_ _} _.
Arguments BinProduct_of_Signatures {_ _ _} _ _ _.
Arguments Sum_of_Signatures _ {_ _ _} _ _.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variables (sort : hSet).

Local Definition HSET_over_sort : category.
Proof.
exists (HSET / sort).
now apply has_homsets_slice_precat.
Defined.

Let BC := BinCoproducts_slice_precat _ BinCoproductsHSET sort: BinCoproducts (HSET / sort).

(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU :=
  ∑ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition mkMultiSortedSig {I : hSet}
  (ar : I → list (list sort × sort) × sort) : MultiSortedSig := (I,,ar).


(** * Construction of an endofunctor on [HSET/sort,HSET/sort] from a multisorted signature *)
Section functor.

Local Definition proj_fun (s : sort) : HSET / sort -> HSET :=
  λ p, hfiber_hSet (pr2 p) s.

Definition proj_functor (s : sort) : functor (HSET / sort) HSET.
Proof.
use tpair.
- exists (proj_fun s).
  intros X Y f p.
  exists (pr1 f (pr1 p)).
  abstract (now induction f as [h hh]; induction p as [x hx]; simpl in *; rewrite <- hx, hh).
- abstract (split; [intros X|intros X Y Z f g];
            apply funextsec; intro p; apply subtypePath; trivial;
            intros x; apply setproperty).
Defined.

(** The left adjoint to the proj_functor *)
Definition hat_functor (t : sort) : functor HSET (HSET / sort).
Proof.
use tpair.
- use tpair.
  + intro A; apply (A,,λ _, t).
  + intros A B f; apply (tpair _ f), idpath.
- abstract (now split; [intros A|intros A B C f g];
            apply subtypePath; try (intro x; apply has_homsets_HSET)).
Defined.

(*
(** The object (1,λ _,s) in HSET/sort that can be seen as a sorted variable *)
Local Definition constHSET_slice (s : sort) : HSET / sort.
Proof.
exists (TerminalObject TerminalHSET); simpl.
apply (λ x, s).
Defined.
 *)
Local Definition constHSET_slice := constHSET_slice sort.

(*
Definition sorted_option_functor (s : sort) : functor (HSET / sort) (HSET / sort) :=
  constcoprod_functor1 (BinCoproducts_HSET_slice sort) (constHSET_slice s).
 *)
Local Definition sorted_option_functor := sorted_option_functor sort.

(** Sorted option functor for lists (also called option in the note) *)
Local Definition option_list (xs : list sort) : functor (HSET / sort) (HSET / sort).
Proof.
(* This should be foldr1 in order to avoid composing with the
   identity functor in the base case *)
use (foldr1 (λ F G, F ∙ G) (functor_identity _) (map sorted_option_functor xs)).
Defined.

(** Define a functor

F^(l,t)(X) := proj_functor(t) ∘ X ∘ option_functor(l)

if l is nonempty and

F^(l,t)(X) := proj_functor(t) ∘ X

otherwise
 *)
Definition exp_functor (lt : list sort × sort) :
  functor [HSET_over_sort,HSET_over_sort] [HSET_over_sort,HSET].
Proof.
induction lt as [l t].
(* use list_ind to do a case on whether l is empty or not *)
use (list_ind _ _ _ l); clear l.
- exact (post_composition_functor (proj_functor t)).
- intros s l _.
  eapply functor_composite.
  + exact (pre_composition_functor (option_list (cons s l))).
  + exact (post_composition_functor (proj_functor t)).
Defined.

(** This defines F^lts where lts is a list of (l,t). Outputs a product of
    functors if the list is nonempty and otherwise the constant functor. *)
Local Definition exp_functor_list (xs : list (list sort × sort)) :
  functor [HSET_over_sort,HSET_over_sort] [HSET_over_sort,HSET].
Proof.
(* If the list is empty we output the constant functor *)
set (T := constant_functor [HSET_over_sort,HSET_over_sort] [HSET_over_sort,HSET]
                           (constant_functor HSET_over_sort HSET TerminalHSET)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
set (XS := map exp_functor xs).
(* This should be foldr1 in order to avoid composing with the
   constant functor in the base case *)
use (foldr1 (λ F G, BinProduct_of_functors _ F G) T XS).
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Definition hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  functor [HSET_over_sort,HSET_over_sort] [HSET_over_sort,HSET_over_sort] :=
    exp_functor_list (pr1 xst) ∙ post_composition_functor (hat_functor (pr2 xst)).

(** The function from multisorted signatures to functors *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig) :
  functor [HSET_over_sort,HSET_over_sort] [HSET_over_sort,HSET_over_sort].
Proof.
use (coproduct_of_functors (ops M)).
+ apply Coproducts_functor_precat, Coproducts_slice_precat, CoproductsHSET, setproperty.
+ intros op.
  exact (hat_exp_functor_list (arity M op)).
Defined.

End functor.


(** * Construction of the strength for the endofunctor on [HSET/sort,HSET/sort] derived from a
      multisorted signature *)
Section strength.

(* The DL for sorted_option_functor *)
Local Definition DL_sorted_option_functor (s : sort) :
  DistributiveLaw _ (sorted_option_functor s) :=
    genoption_DistributiveLaw _ (constHSET_slice s)(BinCoproducts_HSET_slice sort).

(* The DL for option_list *)
Local Definition DL_option_list (xs : list sort) :
  DistributiveLaw _ (option_list xs).
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
Local Definition Sig_exp_functor (lt : list sort × sort) :
  Signature HSET_over_sort HSET HSET_over_sort.
Proof.
exists (exp_functor lt).
induction lt as [l t].
induction l as [[|n] xs].
+ induction xs.
  exact (pr2 (Gθ_Signature (IdSignature _ _) (proj_functor t))).
+ induction n as [|n IH].
  * induction xs as [m []].
    set (Sig_option_list := θ_from_δ_Signature (DL_option_list (cons m (0,,tt)))).
    exact (pr2 (Gθ_Signature Sig_option_list (proj_functor t))).
  * induction xs as [m xs].
    set (Sig_option_list := θ_from_δ_Signature (DL_option_list (cons m (S n,,xs)))).
    exact (pr2 (Gθ_Signature Sig_option_list (proj_functor t))).
Defined.

Local Lemma functor_in_Sig_exp_functor_ok (lt : list sort × sort) :
  Signature_Functor (Sig_exp_functor lt) = exp_functor lt.
Proof.
apply idpath.
Qed.

(* The signature for exp_functor_list *)
Local Definition Sig_exp_functor_list (xs : list (list sort × sort)) :
  Signature HSET_over_sort HSET HSET_over_sort.
Proof.
exists (exp_functor_list xs).
induction xs as [[|n] xs].
- induction xs.
  exact (pr2 (ConstConstSignature HSET_over_sort HSET HSET_over_sort TerminalHSET)).
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
Local Definition Sig_hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  Signature HSET_over_sort HSET_over_sort HSET_over_sort.
Proof.
apply (Gθ_Signature (Sig_exp_functor_list (pr1 xst)) (hat_functor (pr2 xst))).
Defined.

Local Lemma functor_in_Sig_hat_exp_functor_list_ok (xst : list (list sort × sort) × sort) :
  Signature_Functor (Sig_hat_exp_functor_list xst) = hat_exp_functor_list xst.
Proof.
apply idpath.
Qed.

(* The signature for MultiSortedSigToFunctor *)
Definition MultiSortedSigToSignature (M : MultiSortedSig) : Signature HSET_over_sort HSET_over_sort HSET_over_sort.
Proof.
set (Hyps := λ (op : ops M), Sig_hat_exp_functor_list (arity M op)).
use (Sum_of_Signatures (ops M) _ Hyps).
apply Coproducts_slice_precat, CoproductsHSET, setproperty.
Defined.

Local Lemma functor_in_MultiSortedSigToSignature_ok (M : MultiSortedSig) :
  Signature_Functor (MultiSortedSigToSignature M) = MultiSortedSigToFunctor M.
Proof.
apply idpath.
Qed.

End strength.


(** * Proof that the functor obtained from a multisorted signature is omega-cocontinuous *)
Section omega_cocont.

(** The proj functor is naturally isomorphic to the following functor which is a left adjoint: *)
Local Definition proj_functor' (s : sort) : functor (HSET / sort) HSET :=
  functor_composite
     (constprod_functor1 (BinProducts_HSET_slice sort) (constHSET_slice s))
     (slicecat_to_cat HSET sort).

Local Lemma nat_trans_proj_functor (s : sort) : nat_trans (proj_functor' s) (proj_functor s).
Proof.
use make_nat_trans.
- simpl; intros x H.
  exists (pr2 (pr1 H)).
  apply (!pr2 H).
- intros x y f.
  apply funextsec; intro w.
  apply subtypePath; trivial.
  intro z; apply setproperty.
Defined.

Local Lemma is_iso_nat_trans_proj_functor (s : sort) :
  @is_iso [HSET/sort,HSET] _ _ (nat_trans_proj_functor s).
Proof.
use is_iso_qinv.
+ use make_nat_trans.
  - simpl; intros x xy.
    exists (tt,,pr1 xy).
    apply (!pr2 xy).
  - abstract (intros X Y f; apply funextsec; intros x;
              apply subtypePath; trivial; intros w; apply setproperty).
+ abstract (split;
  [ apply subtypePath; [intros x; apply isaprop_is_nat_trans, has_homsets_HSET|];
    apply funextsec; intro x; apply funextsec; intro y; cbn;
    now rewrite pathsinv0inv0; induction y as [y' y3]; induction y' as [y'' y2]; induction y''
  | apply (nat_trans_eq has_homsets_HSET); simpl; intros x;
    apply funextsec; intros z; simpl in *;
    now apply subtypePath; trivial; intros w; apply setproperty]).
Defined.

Local Lemma is_left_adjoint_proj_functor' (s : sort) : is_left_adjoint (proj_functor' s).
Proof.
use is_left_adjoint_functor_composite.
- apply Exponentials_HSET_slice.
- apply is_left_adjoint_slicecat_to_cat_HSET.
Defined.

Local Lemma is_left_adjoint_proj_functor (s : sort) : is_left_adjoint (proj_functor s).
Proof.
apply (is_left_adjoint_iso _ _ (_,,is_iso_nat_trans_proj_functor s)).
apply is_left_adjoint_proj_functor'.
Defined.

Local Lemma is_omega_cocont_post_comp_proj (s : sort) :
  is_omega_cocont (@post_composition_functor (HSET/sort) _ _ (proj_functor s)).
Proof.
apply is_omega_cocont_post_composition_functor.
apply is_left_adjoint_proj_functor.
Defined.

(** The hat_functor is left adjoint to proj_functor *)
Local Lemma is_left_adjoint_hat (s : sort) : is_left_adjoint (hat_functor s).
Proof.
exists (proj_functor s).
use make_are_adjoints.
+ use make_nat_trans.
  - intros X; simpl; intros x; apply (x,,idpath s).
  - intros X Y f; simpl; apply funextsec; intro x; cbn.
    now apply subtypePath; trivial; intros y; apply setproperty.
+ use make_nat_trans.
  - intros X; simpl in *.
    use tpair; simpl.
    * intros H; apply (pr1 H).
    * abstract (apply funextsec; intro x; apply (! pr2 x)).
  - now intros X Y f; apply eq_mor_slicecat.
+ split.
  - now intros X; apply eq_mor_slicecat.
  - intros X; apply funextsec; intro x.
    now apply subtypePath; trivial; intros x'; apply setproperty.
Defined.

Local Lemma is_omega_cocont_exp_functor (a : list sort × sort)
  (H : Colims_of_shape nat_graph HSET_over_sort) :
  is_omega_cocont (exp_functor a).
Proof.
induction a as [xs t].
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_post_comp_proj.
- induction n as [|n].
  + induction xs as [m []].
    use is_omega_cocont_functor_composite.
    * apply is_omega_cocont_pre_composition_functor, H.
    * apply is_omega_cocont_post_comp_proj.
  + induction xs as [m k]; simpl.
    use (@is_omega_cocont_functor_composite _ _ _ (ℓ (option_list _))).
    * apply is_omega_cocont_pre_composition_functor, H.
    * apply is_omega_cocont_post_comp_proj.
Defined.

Local Lemma is_omega_cocont_exp_functor_list (xs : list (list sort × sort))
  (H : Colims_of_shape nat_graph HSET_over_sort) :
  is_omega_cocont (exp_functor_list xs).
Proof.
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_constant_functor.
- induction n as [|n IHn].
  + induction xs as [m []].
    apply is_omega_cocont_exp_functor, H.
  + induction xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors.
    * apply BinProducts_functor_precat, BinProducts_slice_precat, PullbacksHSET.
    * apply is_omega_cocont_constprod_functor1.
      apply Exponentials_functor_HSET.
    * apply is_omega_cocont_exp_functor, H.
    * apply (IHn (k,,xs)).
Defined.

Local Lemma is_omega_cocont_post_comp_hat_functor (s : sort) :
  is_omega_cocont (@post_composition_functor HSET_over_sort  _ _ (hat_functor s)).
Proof.
apply is_omega_cocont_post_composition_functor, is_left_adjoint_hat.
Defined.

Local Lemma is_omega_cocont_hat_exp_functor_list (xst : list (list sort × sort) × sort)
  (H : Colims_of_shape nat_graph HSET_over_sort) :
  is_omega_cocont (hat_exp_functor_list xst).
Proof.
  apply is_omega_cocont_functor_composite.
  + apply is_omega_cocont_exp_functor_list, H.
  + apply is_omega_cocont_post_comp_hat_functor.
Defined.

(** The functor obtained from a multisorted binding signature is omega-cocontinuous *)
Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig)
  (H : Colims_of_shape nat_graph HSET_over_sort) :
  is_omega_cocont (MultiSortedSigToFunctor M).
Proof.
  apply is_omega_cocont_coproduct_of_functors.
  intros op; apply is_omega_cocont_hat_exp_functor_list, H.
Defined.

Lemma is_omega_cocont_MultiSortedSigToSignature
  (M : MultiSortedSig) (H : Colims_of_shape nat_graph HSET_over_sort) :
  is_omega_cocont (MultiSortedSigToSignature M).
Proof.
apply is_omega_cocont_MultiSortedSigToFunctor, H.
Defined.

End omega_cocont.


(** * Construction of a monad from a multisorted signature *)
Section monad.

Let Id_H := Id_H (HSET / sort) (BinCoproducts_HSET_slice sort).

(* ** Construction of initial algebra for a signature with strength on Set / sort *)
Definition SignatureInitialAlgebraSetSort
  (H : Signature HSET_over_sort HSET_over_sort HSET_over_sort) (Hs : is_omega_cocont H) :
  Initial (FunctorAlg (Id_H H)).
Proof.
use colimAlgInitial.
- apply Initial_functor_precat, Initial_slice_precat, InitialHSET.
- apply (is_omega_cocont_Id_H), Hs.
- apply ColimsFunctorCategory_of_shape, slice_precat_colims_of_shape,
        ColimsHSET_of_shape.
Defined.

Let HSS := @hss_category _ (BinCoproducts_HSET_slice sort).

(* ** Multisorted signature to a HSS *)
Definition MultiSortedSigToHSS (sig : MultiSortedSig) :
  HSS (MultiSortedSigToSignature sig).
Proof.
apply SignatureToHSS.
+ apply Initial_slice_precat, InitialHSET.
+ apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
+ apply is_omega_cocont_MultiSortedSigToSignature.
  apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
Defined.

(* The above HSS is initial *)
Definition MultiSortedSigToHSSisInitial (sig : MultiSortedSig) :
  isInitial _ (MultiSortedSigToHSS sig).
Proof.
now unfold MultiSortedSigToHSS, SignatureToHSS; destruct InitialHSS.
Qed.

(** ** Function from multisorted binding signatures to monads *)
Definition MultiSortedSigToMonad (sig : MultiSortedSig) : Monad (HSET / sort).
Proof.
use Monad_from_hss.
- apply BinCoproducts_HSET_slice.
- apply (MultiSortedSigToSignature sig).
- apply MultiSortedSigToHSS.
Defined.

End monad.
End MBindingSig.
