(*

Direct implementation of indexed coproducts together with:

- The general coproduct functor ([coproduct_functor])
- Definition of a coproduct structure on a functor category by taking pointwise coproducts in the
  target category (adapted from the binary version) ([])
- Coproducts from colimits ([Coproducts_from_Colims])

Written by: Anders Mörtberg 2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Local Open Scope cat.

(** * Definition of indexed coproducts of objects in a precategory *)
Section coproduct_def.

Variables (I : UU) (C : precategory).

Definition isCoproductCocone (a : I -> C) (co : C)
  (ia : ∏ i, a i --> co) :=
  ∏ (c : C) (f : ∏ i, a i --> c),
    iscontr (total2 (fun (g : co --> c) => ∏ i, ia i · g = f i)).

Definition CoproductCocone (a : I -> C) :=
   ∑ coia : (∑ co : C, ∏ i, a i --> co),
          isCoproductCocone a (pr1 coia) (pr2 coia).

Definition Coproducts := ∏ (a : I -> C), CoproductCocone a.
Definition hasCoproducts := ishinh Coproducts.

Definition CoproductObject {a : I -> C} (CC : CoproductCocone a) : C := pr1 (pr1 CC).
Definition CoproductIn {a : I -> C} (CC : CoproductCocone a): ∏ i, a i --> CoproductObject CC :=
  pr2 (pr1 CC).

Definition isCoproductCocone_CoproductCocone {a : I -> C} (CC : CoproductCocone a) :
   isCoproductCocone a (CoproductObject CC) (CoproductIn CC).
Proof.
  exact (pr2 CC).
Defined.

Definition CoproductArrow {a : I -> C} (CC : CoproductCocone a) {c : C} (f : ∏ i, a i --> c) :
      CoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isCoproductCocone_CoproductCocone CC _ f))).
Defined.

Lemma CoproductInCommutes (a : I -> C) (CC : CoproductCocone a) :
     ∏ (c : C) (f : ∏ i, a i --> c) i, CoproductIn CC i · CoproductArrow CC f = f i.
Proof.
  intros c f i.
  exact (pr2 (pr1 (isCoproductCocone_CoproductCocone CC _ f)) i).
Qed.

Lemma CoproductIn_idtoiso {i1 i2 : I} (a : I -> C) (CC : CoproductCocone a)
      (e : i1 = i2) :
  idtoiso (maponpaths a e) · CoproductIn CC i2 = CoproductIn CC i1.
Proof.
  induction e.
  apply id_left.
Qed.

Lemma CoproductArrowUnique (a : I -> C) (CC : CoproductCocone a) (x : C)
    (f : ∏ i, a i --> x) (k : CoproductObject CC --> x)
    (Hk : ∏ i, CoproductIn CC i · k = f i) :
  k = CoproductArrow CC f.
Proof.
  set (H' := pr2 (isCoproductCocone_CoproductCocone CC _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Lemma CoproductArrowEta (a : I -> C) (CC : CoproductCocone a) (x : C)
    (f : CoproductObject CC --> x) :
    f = CoproductArrow CC (λ i, CoproductIn CC i · f).
Proof.
  now apply CoproductArrowUnique.
Qed.


Definition CoproductOfArrows {a : I -> C} (CCab : CoproductCocone a) {c : I -> C}
    (CCcd : CoproductCocone c) (f : ∏ i, a i --> c i) :
          CoproductObject CCab --> CoproductObject CCcd :=
    CoproductArrow CCab (λ i, f i · CoproductIn CCcd i).

Lemma CoproductOfArrowsIn {a : I -> C} (CCab : CoproductCocone a) {c : I -> C}
    (CCcd : CoproductCocone c) (f : ∏ i, a i --> c i) :
    ∏ i, CoproductIn CCab i · CoproductOfArrows CCab CCcd f = f i · CoproductIn CCcd i.
Proof.
  unfold CoproductOfArrows; intro i.
  apply CoproductInCommutes.
Qed.

Definition mk_CoproductCocone (a : I -> C) (c : C) (f : ∏ i, a i --> c) :
   isCoproductCocone _ _ f →  CoproductCocone a.
Proof.
intro H.
use tpair.
- apply (tpair _ c f).
- apply H.
Defined.

Definition mk_isCoproductCocone (hsC : has_homsets C) (a : I -> C) (co : C)
  (f : ∏ i, a i --> co) : (∏ (c : C) (g : ∏ i, a i --> c),
                                  ∃! k : C ⟦co, c⟧, ∏ i, f i · k = g i)
   →    isCoproductCocone a co f.
Proof.
  intros H c cc.
  apply H.
Defined.

Lemma precompWithCoproductArrow {a : I -> C} (CCab : CoproductCocone a) {c : I -> C}
    (CCcd : CoproductCocone c) (f : ∏ i, a i --> c i)
    {x : C} (k : ∏ i, c i --> x) :
        CoproductOfArrows CCab CCcd f · CoproductArrow CCcd k =
         CoproductArrow CCab (λ i, f i · k i).
Proof.
apply CoproductArrowUnique; intro i.
now rewrite assoc, CoproductOfArrowsIn, <- assoc, CoproductInCommutes.
Qed.

Lemma postcompWithCoproductArrow {a : I -> C} (CCab : CoproductCocone a) {c : C}
    (f : ∏ i, a i --> c) {x : C} (k : c --> x)  :
       CoproductArrow CCab f · k = CoproductArrow CCab (λ i, f i · k).
Proof.
apply CoproductArrowUnique; intro i.
now rewrite assoc, CoproductInCommutes.
Qed.

Lemma Coproduct_endo_is_identity (a : I -> C) (CC : CoproductCocone a)
  (k : CoproductObject CC --> CoproductObject CC)
  (H1 : ∏ i, CoproductIn CC i · k = CoproductIn CC i)
  : identity _ = k.
Proof.
apply pathsinv0.
eapply pathscomp0; [apply CoproductArrowEta|].
apply pathsinv0, CoproductArrowUnique; intro i; apply pathsinv0.
now rewrite id_right, H1.
Defined.

End coproduct_def.

Section Coproducts.

Variables (I : UU) (C : precategory) (CC : Coproducts I C).

(* Lemma CoproductArrow_eq (f f' : a --> c) (g g' : b --> c) *)
(*   : f = f' → g = g' → *)
(*       CoproductArrow _ (CC _ _) f g = CoproductArrow _ _ f' g'. *)
(* Proof. *)
(*   induction 1. *)
(*   induction 1. *)
(*   apply idpath. *)
(* Qed. *)

Definition CoproductOfArrows_comp (a b c : I -> C)
  (f : ∏ i, a i --> b i) (g : ∏ i, b i --> c i) :
   CoproductOfArrows _ _ _ _ f · CoproductOfArrows _ _ (CC _) (CC _) g
   = CoproductOfArrows _ _ (CC _) (CC _)(λ i, f i · g i).
Proof.
apply CoproductArrowUnique; intro i.
rewrite assoc, CoproductOfArrowsIn.
now rewrite <- assoc, CoproductOfArrowsIn, assoc.
Qed.

Definition CoproductOfArrows_eq (a c : I -> C) (f f' : ∏ i, a i --> c i) : f = f' ->
  CoproductOfArrows _ _ _ _ f = CoproductOfArrows _ _ (CC _) (CC _) f'.
Proof.
now induction 1.
Qed.

End Coproducts.

Section functors.

Definition coproduct_functor_data (I : UU) {C : precategory}
  (PC : Coproducts I C) : functor_data (power_precategory I C) C.
Proof.
use tpair.
- intros p.
  apply (CoproductObject _ _ (PC p)).
- simpl; intros p q f.
  apply (CoproductOfArrows _ _ _ _ f).
Defined.

(** * The coproduct functor: C^I -> C *)
Definition coproduct_functor (I : UU) {C : precategory}
  (PC : Coproducts I C) : functor (power_precategory I C) C.
Proof.
apply (tpair _ (coproduct_functor_data _ PC)).
split.
  - intro x; simpl; apply pathsinv0, Coproduct_endo_is_identity.
    now intro i; rewrite CoproductOfArrowsIn, id_left.
  - now intros x y z f g; simpl; rewrite CoproductOfArrows_comp .
Defined.

End functors.

(* The copropuct of a family of functors *)
(* This is the old and not so good definition as it is unnecessarily complicated, also the proof
   that it is omega-cocontinuous requires that C has products *)
Definition coproduct_of_functors_alt_old (I : UU) {C D : precategory}
  (HD : Coproducts I D) (F : I -> functor C D) : functor C D :=
  functor_composite (delta_functor I C)
     (functor_composite (family_functor _ F)
                        (coproduct_functor _ HD)).

(** The copropuct of a family of functors *)
Definition coproduct_of_functors_alt (I : UU) {C D : precategory}
  (HD : Coproducts I D) (F : ∏ (i : I), functor C D)
  := functor_composite (tuple_functor F) (coproduct_functor _ HD).


(** * Coproducts lift to functor categories *)
Section def_functor_pointwise_coprod.

Variables (I : UU) (C D : precategory).
Variable HD : Coproducts I D.
Variable hsD : has_homsets D.

Section coproduct_of_functors.

Variables (F : I -> functor C D).

Definition coproduct_of_functors_ob (c : C) : D
  := CoproductObject _ _ (HD (λ i, F i c)).

Definition coproduct_of_functors_mor (c c' : C) (f : c --> c')
  : coproduct_of_functors_ob c --> coproduct_of_functors_ob c' :=
  CoproductOfArrows _ _ _ _ (λ i, # (F i) f).

Definition coproduct_of_functors_data : functor_data C D.
Proof.
  exists coproduct_of_functors_ob.
  exact coproduct_of_functors_mor.
Defined.

Lemma is_functor_coproduct_of_functors_data :
  is_functor coproduct_of_functors_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply Coproduct_endo_is_identity; intro i.
    unfold coproduct_of_functors_mor.
    eapply pathscomp0; [apply (CoproductOfArrowsIn _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_left.
- unfold functor_compax; simpl; unfold coproduct_of_functors_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply CoproductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition coproduct_of_functors : functor C D :=
  tpair _ _ is_functor_coproduct_of_functors_data.

Lemma coproduct_of_functors_alt_old_eq_coproduct_of_functors :
  coproduct_of_functors_alt_old _ HD F = coproduct_of_functors.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Lemma coproduct_of_functors_alt_eq_coproduct_of_functors :
  coproduct_of_functors_alt _ HD F = coproduct_of_functors.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition coproduct_nat_trans_in_data i (c : C) :
  D ⟦ (F i) c, coproduct_of_functors c ⟧ :=
  CoproductIn _ _ (HD (λ j, (F j) c)) i.

Lemma is_nat_trans_coproduct_nat_trans_in_data i :
  is_nat_trans _ _ (coproduct_nat_trans_in_data i).
Proof.
intros c c' f; apply pathsinv0.
now eapply pathscomp0;[apply (CoproductOfArrowsIn I _ (HD (λ i, (F i) c)))|].
Qed.

Definition coproduct_nat_trans_in i : nat_trans (F i) coproduct_of_functors :=
  tpair _ _ (is_nat_trans_coproduct_nat_trans_in_data i).

Section vertex.

Variable A : functor C D.
Variable f : ∏ i, nat_trans (F i) A.

Definition coproduct_nat_trans_data c :
  coproduct_of_functors c --> A c :=
    CoproductArrow _ _ _ (λ i, f i c).

Lemma is_nat_trans_coproduct_nat_trans_data :
  is_nat_trans _ _ coproduct_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0.
apply (precompWithCoproductArrow I D (HD (λ i : I, (F i) a)) (HD (λ i : I, (F i) b))).
apply pathsinv0.
eapply pathscomp0; [apply postcompWithCoproductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition coproduct_nat_trans : nat_trans coproduct_of_functors A
  := tpair _ _ is_nat_trans_coproduct_nat_trans_data.

End vertex.

Definition functor_precat_coproduct_cocone
  : CoproductCocone I [C, D, hsD] F.
Proof.
simple refine (mk_CoproductCocone _ _ _ _ _ _).
- apply coproduct_of_functors.
- apply coproduct_nat_trans_in.
- simple refine (mk_isCoproductCocone _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f.
    use tpair.
    * apply (tpair _ (coproduct_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq hsD); intro c;
                apply (CoproductInCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypeEquality; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans hsD)|];
        apply (nat_trans_eq hsD); intro c;
        apply CoproductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End coproduct_of_functors.

Definition Coproducts_functor_precat : Coproducts I [C, D, hsD].
Proof.
  intros F.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.

(** * Coproducts from colimits *)
Section coproducts_from_colimits.

Variables (I : UU) (C : precategory) (hsC : has_homsets C).

Definition I_graph : graph := (I,,λ _ _,empty).

Definition coproducts_diagram (F : I → C) : diagram I_graph C.
Proof.
exists F.
abstract (intros u v e; induction e).
Defined.

Definition CoproductsCocone c (F : I → C) (H : ∏ i, F i --> c) :
  cocone (coproducts_diagram F) c.
Proof.
use tpair.
+ intro v; apply H.
+ abstract (intros u v e; induction e).
Defined.

Lemma Coproducts_from_Colims : Colims_of_shape I_graph C -> Coproducts I C.
Proof.
intros H F.
set (HF := H (coproducts_diagram F)).
use mk_CoproductCocone.
+ apply (colim HF).
+ intros i; apply (colimIn HF).
+ apply (mk_isCoproductCocone _ _ hsC); intros c Fic.
  use unique_exists.
  - apply colimArrow.
    use mk_cocone.
    * simpl; intro i; apply Fic.
    * abstract (simpl; intros u v e; induction e).
  - abstract (simpl; intro i; apply (colimArrowCommutes HF)).
  - abstract (intros y; apply impred; intro i; apply hsC).
  - abstract (intros f Hf; apply colimArrowUnique; simpl in *; intros i; apply Hf).
Defined.

End coproducts_from_colimits.