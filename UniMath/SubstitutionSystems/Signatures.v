
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of signatures
-    Proof that two forms of strength laws are equivalent


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.Notation.


(** Goal: define signatures as pairs of a rank-2 functor and a "strength" *)

(** * Definition of signatures *)

Section fix_a_category.

Variable C : precategory.
Variable hs : has_homsets C.

(** in the original definition, this second category was the same as the first one *)
Variable D : precategory.
Variable hsD : has_homsets D.


Section about_signatures.

(** [H] is a rank-2 functor: a functor between functor categories *)
Variable H : functor [C, C, hs] [C, D, hsD].

(** The forgetful functor from pointed endofunctors to endofunctors *)
Local Notation "'U'" := (functor_ptd_forget C hs).
(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hs).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .



(** ** Source and target of the natural transformation [θ] *)


(** Source is given by [(X,Z) => H(X)∙U(Z)] *)
Definition θ_source_ob (FX : EndC XX Ptd) : [C, D, hsD] := H (pr1 FX) • U (pr2 FX).

Definition θ_source_mor {FX FX' : EndC XX Ptd} (αβ : FX --> FX')
  : θ_source_ob FX --> θ_source_ob FX' := horcomp (#U (pr2 αβ)) (#H (pr1 αβ)).


Definition θ_source_functor_data : functor_data (EndC XX Ptd) [C, D, hsD].
Proof.
  exists θ_source_ob.
  exact (@θ_source_mor).
Defined.

Lemma is_functor_θ_source : is_functor θ_source_functor_data.
Proof.
  split; simpl.
  - intro FX.
    apply nat_trans_eq.
    + apply hsD.
    + intro c. simpl.
      rewrite functor_id.
      rewrite id_right.
      set (HH:=functor_id H).
      rewrite HH. apply idpath.
  - intros FX FX' FX'' α β.
    apply nat_trans_eq.
    + apply hsD.
    + destruct FX as [F X].
      destruct FX' as [F' X'].
      destruct FX'' as [F'' X''].
      intro c ; simpl in *.
      destruct α as [α a].
      destruct β as [β b]. simpl in *.
      rewrite functor_comp.
      rewrite (functor_comp H); simpl.
      repeat rewrite <- assoc.
      apply maponpaths.
      rewrite <- nat_trans_ax.
      destruct a as [a aax].
      destruct b as [b bax]. simpl in *.
      destruct X as [X eta].
      destruct X' as [X' eta'].
      destruct X'' as [X'' eta'']; simpl in *.
      clear aax eta. clear bax eta'. clear eta''.
      set (HHH:=nat_trans_ax (#H β)).
      rewrite <- functor_comp.
      rewrite assoc.
      rewrite <- functor_comp.
      rewrite HHH.
      apply idpath.
Qed.

Definition θ_source : functor _ _ := tpair _ _ is_functor_θ_source.

(** Target is given by [(X,Z) => H(X∙U(Z))] *)

Definition θ_target_ob (FX : EndC XX Ptd) : [C, D, hsD] := H (pr1 FX • U (pr2 FX)).

Definition θ_target_mor (FX FX' : EndC XX Ptd) (αβ : FX --> FX')
  : θ_target_ob FX --> θ_target_ob FX'
  := #H (pr1 αβ ∙∙ #U(pr2 αβ)).

Definition θ_target_functor_data : functor_data (EndC XX Ptd) [C, D, hsD].
Proof.
  exists θ_target_ob.
  exact θ_target_mor.
Defined.


Lemma is_functor_θ_target_functor_data : is_functor θ_target_functor_data.
Proof.
  split; simpl.
  - intro FX; simpl.
    unfold θ_target_mor.
    set (T:= functor_id_id _ _ H).
    apply T; simpl.
    apply nat_trans_eq.
    + apply hs.
    + intro c; simpl.
      rewrite id_left.
      rewrite functor_id.
      apply idpath.
  - intros FX FX' FX''.
    intros α β.
    unfold θ_target_functor_data. simpl in *.
    unfold θ_target_mor.
    set (T:=functor_comp H (pr1 α ∙∙ # U (pr2 α)) (pr1 β ∙∙ # U (pr2 β))).
    simpl in *.
    eapply pathscomp0.
(*    match goal with |[ H :  ?f = _ |- _ ] => transitivity f end. *)
(*    etransitivity. *)
    Focus 2.
      apply T.
(*  unfold θ_target_mor. simpl. *)
    clear T.
    apply maponpaths.
    destruct α as [α a].
    destruct β as [β b]; simpl in *.
    apply nat_trans_eq.
    + apply hs.
    + intro c.
      unfold horcomp; simpl.
      destruct FX as [F X];
      destruct FX' as [F' X'];
      destruct FX'' as [F'' X'']; simpl in *.
      repeat rewrite <- assoc. apply maponpaths.
      rewrite <- (nat_trans_ax β ((pr1 X') c)).
      rewrite assoc.
      rewrite <- functor_comp.
      rewrite nat_trans_ax.
      apply idpath.
Qed.

Definition θ_target : functor _ _ := tpair _ _ is_functor_θ_target_functor_data.

(** * Two alternative versions of the strength laws *)


(** We assume a suitable (bi)natural transformation [θ] *)
Hypothesis θ : θ_source ⟹ θ_target.

(** [θ] is supposed to satisfy two strength laws *)

Definition θ_Strength1 : UU := ∏ X : EndC,
  (θ (X ⊗ (id_Ptd C hs))) · # H (identity X : functor_composite (functor_identity C) X ⟹ pr1 X)
          = nat_trans_id _ .

Section Strength_law_1_intensional.

(** needs the heterogeneous formulation of the monoidal operation to type-check *)
Definition θ_Strength1_int : UU
  := ∏ X : EndC,
     θ (X ⊗ (id_Ptd C hs)) · # H (λ_functor _) = λ_functor _.

Lemma θ_Strength1_int_implies_θ_Strength1 : θ_Strength1_int → θ_Strength1.
Proof.
  unfold θ_Strength1_int, θ_Strength1.
  intros T X.
  assert (TX:= T X).
  apply nat_trans_eq; try assumption.
  intro c; simpl.
  assert (T2 := nat_trans_eq_pointwise TX c).
  simpl in *.
  assert (X0 : λ_functor X = identity (X : EndC)).
  { apply nat_trans_eq; try assumption; intros; apply idpath. }
  rewrite X0 in T2.
  apply T2.
Qed.

(* practically the same proof works in the opposite direction *)
Lemma θ_Strength1_implies_θ_Strength1_int : θ_Strength1 → θ_Strength1_int.
Proof.
  unfold θ_Strength1_int, θ_Strength1.
  intros T X.
  assert (TX:= T X).
  apply nat_trans_eq; try assumption.
  intro c; simpl.
  assert (T2 := nat_trans_eq_pointwise TX c).
  simpl in *.
  assert (X0 : λ_functor X = identity (X : EndC)).
  { apply nat_trans_eq; try assumption; intros; apply idpath. }
  rewrite X0.
  apply T2.
Qed.


End Strength_law_1_intensional.

(*
Hypothesis θ_strength1 : θ_Strength1.
*)

Definition θ_Strength2 : UU := ∏ (X : EndC) (Z Z' : Ptd) (Y : EndC)
           (α : functor_compose hs hs (functor_composite (U Z) (U Z')) X --> Y),
    θ (X ⊗ (Z p• Z' : Ptd)) · # H α =
    θ (X ⊗ Z') •• (U Z) · θ ((functor_compose hs hs (U Z') X) ⊗ Z) ·
       # H (α : functor_compose hs hs (U Z) (X • (U Z')) --> Y).

Section Strength_law_2_intensional.
 (* does not typecheck in the heterogeneous formulation *)
Definition θ_Strength2_int : UU
  := ∏ (X : EndC) (Z Z' : Ptd),
      θ (X ⊗ (Z p• Z'))  · #H (α_functor (U Z) (U Z') X )  =
      (α_functor (U Z) (U Z') (H X) : [C, D, hsD] ⟦ functor_compose hs hsD (functor_composite (U Z) (U Z')) (H X), functor_composite (U Z) (functor_composite (U Z') (H X)) ⟧
      ) ·
      θ (X ⊗ Z') •• (U Z) · θ ((functor_compose hs hs (U Z') X) ⊗ Z) .

Lemma θ_Strength2_int_implies_θ_Strength2 : θ_Strength2_int → θ_Strength2.
Proof.
  unfold θ_Strength2_int, θ_Strength2.
  intros T X Z Z' Y a.
  apply nat_trans_eq; try assumption.
  intro c.

  assert (TXZZ' := T X Z Z').
  assert (TXZZ'c := nat_trans_eq_pointwise TXZZ' c).
  simpl in TXZZ'c.
  clear T TXZZ'.
  rewrite id_left in TXZZ'c.
  simpl. rewrite <- TXZZ'c; clear TXZZ'c.
  rewrite <- assoc.
  apply maponpaths.
  assert (functor_comp_H := functor_comp H (α_functor (pr1 Z) (pr1 Z') X)
           (a : functor_compose hs hs (U Z) (functor_composite (U Z') X) --> Y)).
  assert (functor_comp_H_c := nat_trans_eq_pointwise functor_comp_H c).
  simpl in functor_comp_H_c.
  eapply pathscomp0.
    Focus 2. apply functor_comp_H_c.
  clear functor_comp_H functor_comp_H_c.
  revert c.
  apply nat_trans_eq_pointwise.
  apply maponpaths.
  apply nat_trans_eq; try assumption.
  intro c; apply pathsinv0, id_left.
Qed.

(* for curiosity also the other direction *)
Lemma θ_Strength2_implies_θ_Strength2_int : θ_Strength2 → θ_Strength2_int.
Proof.
  unfold θ_Strength2_int, θ_Strength2.
  intros T X Z Z'.
  assert (TXZZ'_inst := T X Z Z' (functor_compose hs hs (U Z)
          (functor_composite (U Z') X)) (α_functor (pr1 Z) (pr1 Z') X)).
  eapply pathscomp0. apply TXZZ'_inst.
  clear T TXZZ'_inst.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  rewrite <- assoc.
  apply maponpaths.
  eapply pathscomp0; [| apply id_right].
  apply maponpaths.
  assert (functor_id_H := functor_id H (functor_compose hs hs (pr1 Z) (functor_composite (pr1 Z') X))).
  assert (functor_id_H_c := nat_trans_eq_pointwise functor_id_H c).
  eapply pathscomp0; [| apply functor_id_H_c].
  clear functor_id_H functor_id_H_c.
  revert c.
  apply nat_trans_eq_pointwise.
  apply maponpaths.
  apply nat_trans_eq; try assumption;
  intro c; apply idpath.
Qed.

End Strength_law_2_intensional.

(*
Hypothesis θ_strength2 : θ_Strength2.
*)

(** Not having a general theory of binatural transformations, we isolate
    naturality in each component here *)

Lemma θ_nat_1 (X X' : EndC) (α : X --> X') (Z : Ptd)
  : compose(C:=[C, D, hsD]) (# H α ∙∙ nat_trans_id (pr1 (U Z))) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z)· # H (α ∙∙ nat_trans_id (pr1 (U Z))).
Proof.
  set (t:=nat_trans_ax θ).
  set (t':=t (X ⊗ Z) (X' ⊗ Z)).
  set (t'':= t' (precatbinprodmor α (identity _ ))).
  simpl in t''.
  exact t''.
Qed.

(* the following makes sense but is wrong
Lemma θ_nat_1' (X X' : EndC) (α : X --> X') (Z : Ptd)
  : compose(C:=EndC) (# H α øø (U Z)) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z)· # H (α øø (U Z)).
Proof.
Abort.
*)

Lemma θ_nat_1_pointwise (X X' : EndC) (α : X --> X') (Z : Ptd) (c : C)
  :  pr1 (# H α) ((pr1 Z) c)· pr1 (θ (X' ⊗ Z)) c =
       pr1 (θ (X ⊗ Z)) c· pr1 (# H (α ∙∙ nat_trans_id (pr1 Z))) c.
Proof.
  set (t := θ_nat_1 _ _ α Z).
  set (t' := nat_trans_eq_weq hsD _ _ t c);
  clearbody t';  simpl in t'.
  assert (H':= functor_id (H X') (pr1 (pr1 Z) c));
  simpl in H'.
  match goal with |[H1 : ?f · _ · ?g = _ , H2 : ?x = _ |- _ ] =>
                        intermediate_path (f · x · g) end.
  - repeat rewrite <- assoc.
    apply maponpaths.
    rewrite H'.
    apply pathsinv0, id_left.
  - apply t'.
Qed.

Lemma θ_nat_2 (X : EndC) (Z Z' : Ptd) (f : Z --> Z')
  : compose (C:=[C, D, hsD]) (identity (H X) ∙∙ pr1 f) (θ (X ⊗ Z')) =
       θ (X ⊗ Z)· # H (identity X ∙∙ pr1 f).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (precatbinprodpair X Z) (precatbinprodpair X Z') (precatbinprodmor (identity _ ) f)).
  simpl in t'.
  unfold θ_source_mor in t'.
  unfold θ_target_mor in t'.
  simpl in t'.
  set (T := functor_id H X).
  simpl in *.
  rewrite T in t'. clear T.
  exact t'.
Qed.

Lemma θ_nat_2_pointwise (X : EndC) (Z Z' : Ptd) (f : Z --> Z') (c : C)
  :  # (pr1 (H X)) ((pr1 f) c)· pr1 (θ (X ⊗ Z')) c =
       pr1 (θ (X ⊗ Z)) c· pr1 (# H (identity X ∙∙ pr1 f)) c .
Proof.
  set (t:=θ_nat_2 X _ _ f).
  set (t':=nat_trans_eq_weq hsD _ _ t c).
  clearbody t'; clear t.
  simpl in t'.
  rewrite id_left in t'.
  exact t'.
Qed.

End about_signatures.

Section Strength_laws.
(** define strength laws *)

End Strength_laws.

Definition Signature (*C : precategory) (hs : has_homsets C*) : UU
  :=
  ∑ H : functor [C, C, hs] [C, D, hsD] ,
     ∑ θ : nat_trans (θ_source H) (θ_target H) , θ_Strength1_int H θ × θ_Strength2_int H θ.

Coercion Signature_Functor (S : Signature) : functor _ _ := pr1 S.

Definition theta (H : Signature) : nat_trans (θ_source H) (θ_target H) := pr1 (pr2 H).

Definition Sig_strength_law1 (H : Signature) : θ_Strength1_int _ _ := pr1 (pr2 (pr2 H)).

Definition Sig_strength_law2 (H : Signature) : θ_Strength2_int _ _ := pr2 (pr2 (pr2 H)).

End fix_a_category.



Arguments theta {_ _ _ _} _ .
Arguments θ_source {_ _ _ _ } _ .
Arguments θ_target {_ _ _ _ } _ .
Arguments θ_Strength1 {_ _ _ _ _ } _ .
Arguments θ_Strength2 {_ _ _ _ _ } _ .
Arguments θ_Strength1_int {_ _ _ _ _} _ .
Arguments θ_Strength2_int {_ _ _ _ _} _ .
