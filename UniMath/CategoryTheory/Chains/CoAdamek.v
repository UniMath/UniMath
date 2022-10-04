(** * Adámek's theorem

The main result is Adámek's theorem for constructing terminal coalgebras of
omega-continuous functors which is used to construct coinductive types.

Written by: Kobe Wullaert, 2022
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Propositions.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.

Local Open Scope cat.

Definition is_omega_cont' {C D : category} (F : functor C D) : UU :=
  ∏ (c : cochain C) (L : C) (cc : cone c L),
    preserves_limit F c L cc.

Section lim_terminal_coalgebra.

Context {C : category} (TerminalC : Terminal C).
Context {F : functor C C} (HF : is_omega_cont' F).

Let Fcochain : cochain C := termCochain TerminalC F.

Variable (CC : LimCone Fcochain).

Let L : C := lim CC.
Let FFcochain : cochain C := mapcochain F Fcochain.
Let Fa : cone FFcochain (F L) := mapcone F _ (limCone CC).

Let FHC' : isLimCone FFcochain (F L) Fa :=
      HF Fcochain L (limCone CC) (isLimCone_LimCone CC).
Let FHC : LimCone FFcochain := make_LimCone _ _ _ FHC'.

Local Definition shiftCone : cone FFcochain L.
Proof.
use make_cone.
- intro n; apply (coneOut (limCone CC) (S n)).
- intros m n e ; destruct e.
  refine (_ @ coneOutCommutes (limCone CC) _ (S n) (idpath _)).
  apply maponpaths.
  simpl.
  rewrite ! idpath_transportf.
  rewrite ! id_left.
  apply idpath.
Defined.

Local Lemma unshiftCone_forms_cone {x : C} ( cc : cone FFcochain x)
  :  forms_cone Fcochain (λ n : vertex conat_graph,
     nat_rect (λ n0 : nat, C ⟦ x, dob Fcochain n0 ⟧) (TerminalArrow TerminalC x)
              (λ (n0 : nat) (_ : C ⟦ x, dob Fcochain n0 ⟧), coneOut cc n0) n).
Proof.
  intros m n e ; destruct e ; destruct n as [|n].
  - apply TerminalArrowUnique.
  - simpl.
    rewrite idpath_transportf ; rewrite id_left.
    rewrite (! coneOutCommutes cc _ n  (idpath _)).
    apply maponpaths.
    simpl.
    rewrite idpath_transportf, id_left.
    apply idpath.
Qed.


Local Definition unshiftCone (x : C) (cc : cone FFcochain x) : cone Fcochain x.
Proof.
use make_cone.
- intro n.
  induction n as [|n].
  + apply TerminalArrow.
  + apply (coneOut cc _).
- apply unshiftCone_forms_cone.
Defined.

Local Definition shiftIsLimCone : isLimCone FFcochain L shiftCone.
Proof.
intros x cc; simpl.
use tpair.
+ use tpair.
  * apply limArrow, (unshiftCone _ cc).
  * abstract (intro n; apply (limArrowCommutes CC x (unshiftCone x cc) (S n))).
+ abstract (intros p; apply subtypePath;
             [ intro f; apply impred; intro; apply homset_property
             | apply limArrowUnique; intro n;
               destruct n as [|n]; [ apply TerminalArrowUnique | apply (pr2 p) ]]).
Defined.

Local Definition shiftLimCone : LimCone FFcochain :=
  make_LimCone FFcochain L shiftCone shiftIsLimCone.

Definition lim_algebra_mor : C⟦L,F L⟧ := limArrow FHC L shiftCone.

Local Definition is_z_iso_lim_algebra_mor : is_z_isomorphism lim_algebra_mor :=
  isLim_is_z_iso _ FHC _ _ shiftIsLimCone.

Let α : z_iso L (F L) := make_z_iso' _ is_z_iso_lim_algebra_mor.
Let α_inv : z_iso (F L) L := z_iso_inv_from_z_iso α.
Let α_alg : coalgebra F := tpair (λ X : C, C ⟦ X , F X⟧) L α.

Lemma unfold_inv_from_z_iso_α :
  inv_from_z_iso α = limArrow shiftLimCone _ (limCone FHC).
Proof.
apply idpath.
Qed.

(** Given an coalgebra:
<<
          a
      A ------> F A
>>
 we now define a coalgebra morphism ad:
<<
        α
   L ------>  F L
    |          |
    |          |
    |          |
    V   a      V
   A ------>  F A
>>

*)
Section coalgebra_mor.

Variable (Aa : coalgebra F).

Local Notation A := (coalgebra_ob _ Aa).
Local Notation a := (coalgebra_mor _ Aa).

Local Definition cone_over_coalg (n : nat) : C ⟦ A, iter_functor F n TerminalC⟧.
Proof.
induction n as [|n Fn]; simpl.
- apply TerminalArrow.
- apply (a · #F Fn).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cone_over_coalg.

Lemma isConeOverCoalg {u v : nat} (e : S v = u) : an u · dmor Fcochain e = an v.
Proof.
  destruct e.
  induction v as [| n IHn].
  - apply TerminalArrowUnique.
  - simpl ; rewrite assoc' ; apply cancel_precomposition.
    etrans.
    2: { apply maponpaths ; exact IHn. }
    rewrite functor_comp.
    simpl.
    do 2 rewrite functor_comp.
    apply maponpaths.
    unfold dmor.
    cbn.
    rewrite ! id_left.
    apply idpath.
Qed.

(* ad = a† = a dagger *)
Local Definition ad : C⟦A,L⟧.
Proof.
apply limArrow.
use make_cone.
- apply cone_over_coalg.
- red ; intro ; intros ; apply isConeOverCoalg.
Defined.

Lemma ad_is_coalgebra_mor (n : nat) :  a · # F ad · inv_from_z_iso α · limOut CC n = an n.
Proof.
  destruct n as [|n].
  - now apply TerminalArrowUnique.
  - rewrite unfold_inv_from_z_iso_α.
    eapply pathscomp0.
    {
      rewrite assoc'.
      apply maponpaths.
      apply (limArrowCommutes shiftLimCone).
    }
    simpl; rewrite assoc', <- functor_comp.
    apply cancel_precomposition, maponpaths, (limArrowCommutes CC).
Qed.

Local Definition ad_mor : coalgebra_homo F Aa α_alg.
Proof.
  exists ad.
  abstract (apply pathsinv0, z_iso_inv_to_right, pathsinv0, limArrowUnique; simpl; intro n ; apply ad_is_coalgebra_mor).
Defined.

End coalgebra_mor.

Lemma limCoAlgIsTerminal_subproof (Aa : CoAlg_category F)
        (Fa' : coalgebra_homo F Aa α_alg) : Fa' = ad_mor Aa.
Proof.
  apply coalgebra_homo_eq.
  { apply homset_property. }
  apply limArrowUnique ; intro n.
  destruct Fa' as [f hf]; simpl.
  unfold is_coalgebra_homo in hf; simpl in hf.
  induction n as [|n IHn]; simpl.
  - apply TerminalArrowUnique.
  - rewrite <- IHn, functor_comp, assoc.
    etrans.
    2: { apply cancel_postcomposition ; apply (! hf). }
    rewrite assoc'.
    apply maponpaths.
    apply (z_iso_inv_to_left _ _ _ α).
    apply (limArrowCommutes shiftLimCone).
Qed.

Lemma limCoAlgIsTerminal : isTerminal (CoAlg_category F) α_alg.
Proof.
  apply make_isTerminal; intros Aa.
  exists (ad_mor Aa).
  apply limCoAlgIsTerminal_subproof.
Defined.

Definition limCoAlgTerminal : Terminal (CoAlg_category F) :=
  make_Terminal _ limCoAlgIsTerminal.

End lim_terminal_coalgebra.
