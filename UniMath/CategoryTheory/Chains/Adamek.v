(** * Adámek's theorem

The main result is Adámek's theorem for constructing initial algebras of
omega-cocontinuous functors ([colimAlgIsInitial]) which is used to construct
inductive types.

Written by: Anders Mörtberg and Benedikt Ahrens, 2015-2016
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.

Require Import UniMath.CategoryTheory.Chains.Chains.

Local Open Scope cat.

(** * Adámek's theorem for constructing initial algebras of omega-cocontinuous functors *)
(** This section proves that (L,α : F L -> L) is the initial algebra
    where L is the colimit of the inital chain:
<<
         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...
>>
This result is also known as Adámek's theorem % \cite{Adamek1974}: \par %

  https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor#AdameksTheorem

Adámek, Jiří. "Free algebras and automata realizations in the language of categories."
Commentationes Mathematicae Universitatis Carolinae 015.4 (1974): 589-602.

*)
Section colim_initial_algebra.

Context {C : precategory} (hsC : has_homsets C) (InitC : Initial C).

(* It is important that these are not packaged together as it is
   sometimes necessary to control how opaque HF is. See
   isalghom_pr1foldr in lists.v *)
Context {F : functor C C} (HF : is_omega_cocont F).

Let Fchain : chain C := initChain InitC F.

Variable (CC : ColimCocone Fchain).

Let L : C := colim CC.
Let FFchain : chain C := mapchain F Fchain.
Let Fa : cocone FFchain (F L) := mapcocone F _ (colimCocone CC).
Let FHC' : isColimCocone FFchain (F L) Fa :=
  HF Fchain L (colimCocone CC) (isColimCocone_from_ColimCocone CC).
Let FHC : ColimCocone FFchain := make_ColimCocone _ _ _ FHC'.

Local Definition shiftCocone : cocone FFchain L.
Proof.
use make_cocone.
- intro n; apply (coconeIn (colimCocone CC) (S n)).
- abstract (intros m n e; destruct e ;
            apply (coconeInCommutes (colimCocone CC) (S m) _ (idpath _))).
Defined.

Local Definition unshiftCocone (x : C) (cc : cocone FFchain x) : cocone Fchain x.
Proof.
use make_cocone.
- simpl; intro n.
  induction n as [|n]; simpl.
  + apply InitialArrow.
  + apply (coconeIn cc _).
- abstract (simpl; intros m n e; destruct e;
            destruct m as [|m]; [ apply InitialArrowUnique
                                | apply (coconeInCommutes cc m _ (idpath _))]).
Defined.

Local Definition shiftIsColimCocone : isColimCocone FFchain L shiftCocone.
Proof.
intros x cc; simpl.
use tpair.
+ use tpair.
  * apply colimArrow, (unshiftCocone _ cc).
  * abstract (intro n; apply (colimArrowCommutes CC x (unshiftCocone x cc) (S n))).
+ abstract (intros p; apply subtypePath;
             [ intro f; apply impred; intro; apply hsC
             | apply colimArrowUnique; intro n;
               destruct n as [|n]; [ apply InitialArrowUnique | apply (pr2 p) ]]).
Defined.

Local Definition shiftColimCocone : ColimCocone FFchain :=
  make_ColimCocone FFchain L shiftCocone shiftIsColimCocone.

Definition colim_algebra_mor : C⟦F L,L⟧ := colimArrow FHC L shiftCocone.

Local Definition is_iso_colim_algebra_mor : is_iso colim_algebra_mor :=
  isColim_is_iso _ FHC _ _ shiftIsColimCocone.

Let α : iso (F L) L := make_iso _ is_iso_colim_algebra_mor.
Let α_inv : iso L (F L) := iso_inv_from_iso α.
Let α_alg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L α.

Lemma unfold_inv_from_iso_α :
  inv_from_iso α = colimArrow shiftColimCocone _ (colimCocone FHC).
Proof.
apply id_right.
Qed.

(** Given an algebra:
<<
          a
   F A ------> A
>>
 we now define an algebra morphism ad:
<<
          α
   F L ------> L
    |          |
    |          | ad
    |          |
    V     a    V
   F A ------> A
>>

*)
Section algebra_mor.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Local Definition cocone_over_alg (n : nat) : C ⟦ dob Fchain n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn · a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor Fchain e · an Sn = an n.
Proof.
destruct e.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- simpl; rewrite assoc.
  apply cancel_postcomposition, pathsinv0.
  eapply pathscomp0; [|simpl; apply functor_comp].
  now apply maponpaths, pathsinv0, IHn.
Qed.

(* ad = a† = a dagger *)
Local Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
use make_cocone.
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma ad_is_algebra_mor : is_algebra_mor _ α_alg Aa ad.
Proof.
apply pathsinv0, iso_inv_to_left, colimArrowUnique; simpl; intro n.
destruct n as [|n].
- now apply InitialArrowUnique.
- rewrite assoc, unfold_inv_from_iso_α.
  eapply pathscomp0;
    [apply cancel_postcomposition, (colimArrowCommutes shiftColimCocone)|].
  simpl; rewrite assoc, <- functor_comp.
  apply cancel_postcomposition, maponpaths, (colimArrowCommutes CC).
Qed.

Local Definition ad_mor : algebra_mor F α_alg Aa := tpair _ _ ad_is_algebra_mor.

End algebra_mor.

Lemma colimAlgIsInitial_subproof (Aa : FunctorAlg F hsC)
        (Fa' : algebra_mor F α_alg Aa) : Fa' = ad_mor Aa.
Proof.
apply (algebra_mor_eq _ hsC); simpl.
apply colimArrowUnique; simpl; intro n.
destruct Fa' as [f hf]; simpl.
unfold is_algebra_mor in hf; simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition, pathsinv0, (iso_inv_to_right _ _ _ _ _ α).
  rewrite unfold_inv_from_iso_α; apply pathsinv0.
  now eapply pathscomp0; [apply (colimArrowCommutes shiftColimCocone)|].
Qed.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) α_alg.
Proof.
apply make_isInitial; intros Aa.
exists (ad_mor Aa).
apply colimAlgIsInitial_subproof.
Defined.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  make_Initial _ colimAlgIsInitial.

End colim_initial_algebra.
