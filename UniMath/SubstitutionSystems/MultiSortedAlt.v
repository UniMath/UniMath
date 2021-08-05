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

Variables (sort : UU) (eq : isdeceq sort). (* Can we eliminate this assumption? *)
Variables (C : category) (BP : BinProducts C) (BC : BinCoproducts C) (TC : Terminal C)
          (CC : forall (I : UU), Coproducts I C).

(* TODO: don't need all the assumption above now *)
Variables (LC : Lims C).

(** Define the discrete category of sorts *)
Let sort_cat : precategory := path_pregroupoid sort.

Let hsC : has_homsets C := homset_property C.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].

Local Lemma hs : has_homsets sortToC.
Proof.
apply homset_property.
Qed.

Local Definition BinProductsSortToCToC : BinProducts [sortToC,C].
Proof.
apply (BinProducts_functor_precat _ _ BP).
Defined.

(* TODO: do something about these assumptions *)
Variable (hat_functor : sort → functor C sortToC).
Variable (is_left_adjoint_hat : forall (s : sort), is_left_adjoint (hat_functor s)).
Variable (foo : Exponentials (BinProducts_functor_precat sortToC C BP (homset_property C))).


Local Definition make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid f.

Local Definition proj_gen_fun (D : precategory) (E : category) (d : D) : functor [D,E] E.
Proof.
use tpair.
+ use tpair.
  - intro f; apply (pr1 f d).
  - simpl; intros a b f; apply (f d).
+ abstract (split; [intro f; apply idpath|intros f g h fg gh; apply idpath]).
Defined.

Local Definition proj_gen {D : precategory} {E : category} : functor D [[D,E],E].
Proof.
use tpair.
+ use tpair.
  - apply proj_gen_fun.
  - intros d1 d2 f.
    use tpair.
    * red; simpl; intro F; apply (# F f).
    * abstract (intros F G α; simpl in *; apply pathsinv0, (nat_trans_ax α d1 d2 f)).
+ abstract (split;
  [ intros F; simpl; apply nat_trans_eq; [apply homset_property|]; intro G; simpl; apply functor_id
  | intros F G H α β; simpl; apply nat_trans_eq; [apply homset_property|];
    intro γ; simpl; apply functor_comp ]).
Defined.

(** Given a sort s this applies the sortToC to s and returns C *)
Definition projSortToC (s : sort) : functor sortToC C.
Proof.
apply proj_gen_fun, s.
Defined.

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)).


Let one_cat : precategory := path_pregroupoid unit.

(* t : 1 → C *)
Definition t_fun (s : sort) : functor one_cat sort_cat.
Proof.
use make_functor.
- use make_functor_data; [intros _; exact s|intros x y H; apply idpath].
- abstract (split; intros x *; apply idpath).
Defined.

Definition C_one_to_C : [one_cat, C] ⟶ C.
Proof.
    use make_functor.
    + use make_functor_data.
      * intros f; apply f; exact tt.
      * intros a b h; apply h.
    + abstract (split; [intros x; apply idpath|intros x *; apply idpath]).
Defined.

Definition projSortToC' (s : sort) : functor sortToC C.
Proof.
  use functor_composite; [use [one_cat,C] | | ].
  - use pre_composition_functor.
    + abstract (apply has_homsets_path_pregroupoid, hlevelntosn, isasetifdeceq, eq).
    + apply t_fun, s.
  - apply C_one_to_C.
Defined.

Lemma is_left_adjoint_projSortToC' (s : sort) : is_left_adjoint (projSortToC' s).
Proof.
  apply is_left_adjoint_functor_composite.
  + apply (RightKanExtension_from_limits (t_fun s)), LC.
  + use tpair.
    - use make_functor.
      * use make_functor_data.
        use make_functor.
        use make_functor_data.
        intros x.
        use make_functor.
        use make_functor_data; [intros _; exact x|intros a b f; apply identity].
        abstract (split; intros a *; [apply idpath | apply pathsinv0, id_left]).
        intros a b f.
        use make_nat_trans.
        intros x; apply f.
        abstract (now intros x y g; rewrite id_left, id_right).
        split.
        abstract (now intros x; use nat_trans_eq; [apply homset_property|]).
        abstract (now intros x y z f g; use nat_trans_eq; [apply homset_property|]).
        intros a b f.
        use make_nat_trans; [intros x; apply f|].
        abstract (now intros a1 y g; rewrite id_left, id_right).
      * split.
        abstract (now intros x; use nat_trans_eq; [apply homset_property|]).
        abstract (now intros x y z f g; use nat_trans_eq; [apply homset_property|]).
    - use tpair.
      * split.
        use make_nat_trans.
        intros x.
        use make_nat_trans.
        intros []; apply identity.
        abstract (intros [] [] f;
        rewrite id_left, id_right; cbn; rewrite <- (functor_id x);
        apply maponpaths, isasetunit).
        abstract (now intros a b f; apply nat_trans_eq; [apply homset_property|];
        intros []; cbn; rewrite id_left, id_right).
        use tpair.
        intros x; apply identity.
        abstract (now intros a b f; rewrite id_left, id_right).
      * cbn; use tpair; intros x.
        abstract (cbn; now rewrite id_left).
        cbn.
        use nat_trans_eq; [apply homset_property|]; intros [].
        cbn.
        now rewrite id_left.
Defined.


Local Lemma nat_trans_projSortToC (s : sort) : nat_trans (projSortToC' s) (projSortToC s).
Proof.
use make_nat_trans.
- simpl; intros x; apply identity.
- abstract (now intros x y f; rewrite id_left, id_right).
Defined.

Local Lemma is_iso_nat_trans_projSortToC (s : sort) :
  @is_iso [_,_] _ _ (nat_trans_projSortToC s).
Proof.
  use is_iso_qinv.
  + use make_nat_trans.
    - simpl; intros x; apply identity.
    - abstract (now intros x y f; rewrite id_left, id_right).
  + split.
    - abstract (apply nat_trans_eq; [apply homset_property|]; intros x; apply id_right).
    - abstract (apply nat_trans_eq; [apply homset_property|]; intros x; apply id_right).
Defined.

Local Lemma is_left_adjoint_projSortToC (s : sort) : is_left_adjoint (projSortToC s).
Proof.
apply (is_left_adjoint_iso _ _ _ (_,,is_iso_nat_trans_projSortToC s)).
apply is_left_adjoint_projSortToC'.
Defined.



(* Code for option as a function, below is the definition as a functor *)
Local Definition option_fun : sort -> sortToC -> sortToC.
Proof.
intros s f.
apply make_sortToC; intro t.
induction (eq s t) as [H|H].
- apply (pr1 f t ⊕ 1).
- apply (pr1 f t).
Defined.

(* The function part of Definition 3 *)
Local Definition option_functor_data  (s : sort) : functor_data sortToC sortToC.
Proof.
use tpair.
+ apply (option_fun s).
+ cbn. intros F G α.
  use tpair.
  * red; simpl; intro t.
    induction (eq s t) as [p|p]; simpl; clear p.
    { apply (BinCoproductOfArrows _ _ _ (α t) (identity _)). }
    { apply α. }
  * abstract (now intros t1 t2 []; cbn; induction (eq s t1); simpl; rewrite id_left, id_right).
Defined. (* plenty of match in the term *)

Local Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split.
+ intros F; apply (nat_trans_eq hsC); intro t; simpl.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply pathsinv0, BinCoproductArrowUnique; rewrite id_left, id_right.
+ intros F G H αFG αGH; apply (nat_trans_eq hsC); intro t; simpl.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  apply pathsinv0; eapply pathscomp0; [apply precompWithBinCoproductArrow|].
  rewrite !id_left; apply BinCoproductArrowUnique.
  * now rewrite BinCoproductIn1Commutes, assoc.
  * now rewrite BinCoproductIn2Commutes, id_left.
Qed. (* match expressions in the term *)

(* This is Definition 3 (sorted context extension) from the note *)
Local Definition option_functor (s : sort) : functor sortToC sortToC :=
  tpair _ _ (is_functor_option_functor s).

(** Sorted option functor for lists (also called option in the note) *)
Local Definition option_list (xs : list sort) : functor sortToC sortToC.
Proof.
(* This should be foldr1 in order to avoid composing with the
   identity functor in the base case *)
use (foldr1 (λ F G, F ∙ G) (functor_identity _) (map option_functor xs)).
Defined.

(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU :=
  ∑ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition mkMultiSortedSig {I : hSet}
  (ar : I → list (list sort × sort) × sort) : MultiSortedSig := (I,,ar).

(** Define a functor

F^(l,t)(X) := proj_functor(t) ∘ X ∘ option_functor(l)

if l is nonempty and

F^(l,t)(X) := proj_functor(t) ∘ X

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
+ apply Coproducts_functor_precat, Coproducts_functor_precat, CC.
+ intros op.
  exact (hat_exp_functor_list (arity M op)).
Defined.

Local Lemma is_omega_cocont_post_comp_projSortToC (s : sort) :
  is_omega_cocont (@post_composition_functor sortToC _ _ hs hsC (projSortToC s)).
Proof.
apply is_omega_cocont_post_composition_functor.
apply is_left_adjoint_projSortToC.
Defined.

Local Lemma is_omega_cocont_exp_functor (a : list sort × sort)
  (H : Colims_of_shape nat_graph sortToC) :
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
    * use is_omega_cocont_pre_composition_functor.
      apply hs.
      apply H.
    * apply is_omega_cocont_post_comp_projSortToC.
  + induction xs as [m k]; simpl.
    use is_omega_cocont_functor_composite.
    (* use (@is_omega_cocont_functor_composite _ _ _ _ (ℓ (option_list _))). *)
    * apply functor_category_has_homsets.
    * exact (is_omega_cocont_pre_composition_functor (option_list (cons m (S n,,k))) hs hs H).
    * apply is_omega_cocont_post_comp_projSortToC.
Defined.

Local Lemma is_omega_cocont_exp_functor_list (xs : list (list sort × sort))
  (H : Colims_of_shape nat_graph sortToC) :
  is_omega_cocont (exp_functor_list xs).
Proof.
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_constant_functor, functor_category_has_homsets.
- induction n as [|n IHn].
  + induction xs as [m []].
    apply is_omega_cocont_exp_functor, H.
  + induction xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors; try apply homset_property.
    * apply BinProducts_functor_precat, BinProducts_functor_precat, BP.
    * apply is_omega_cocont_constprod_functor1; try apply functor_category_has_homsets.
      apply foo.
    * apply is_omega_cocont_exp_functor, H.
    * apply (IHn (k,,xs)).
Defined.

Local Lemma is_omega_cocont_post_comp_hat_functor (s : sort) :
  is_omega_cocont (@post_composition_functor sortToC  _ _
       hsC hs (hat_functor s)).
Proof.
apply is_omega_cocont_post_composition_functor, is_left_adjoint_hat.
Defined.

Local Lemma is_omega_cocont_hat_exp_functor_list (xst : list (list sort × sort) × sort)
  (H : Colims_of_shape nat_graph sortToC) :
  is_omega_cocont (hat_exp_functor_list xst).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_exp_functor_list, H.
+ apply is_omega_cocont_post_comp_hat_functor.
Defined.

(** The functor obtained from a multisorted binding signature is omega-cocontinuous *)
Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig)
  (H : Colims_of_shape nat_graph sortToC) :
  is_omega_cocont (MultiSortedSigToFunctor M).
Proof.
apply is_omega_cocont_coproduct_of_functors; try apply homset_property.
intros op; apply is_omega_cocont_hat_exp_functor_list, H.
Defined.

End MBindingSig.
