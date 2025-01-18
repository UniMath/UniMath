(*

Direct implementation of indexed coproducts together with:

- The general coproduct functor ([coproduct_functor])
- Definition of a coproduct structure on a functor category by taking pointwise coproducts in the
  target category (adapted from the binary version) ([])
- Coproducts from colimits ([Coproducts_from_Colims])

Written by: Anders Mörtberg 2016

Extended by Ralph Matthes 2023 for the distributors

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** * Definition of indexed coproducts of objects in a precategory *)
Section coproduct_def.

Context (I : UU) (C : category).

Definition isCoproduct (a : I -> C) (co : C)
  (ia : ∏ i, a i --> co) :=
  ∏ (c : C) (f : ∏ i, a i --> c),
    ∃! (g : co --> c), ∏ i, ia i · g = f i.

Definition Coproduct (a : I -> C) :=
   ∑ coia : (∑ co : C, ∏ i, a i --> co),
          isCoproduct a (pr1 coia) (pr2 coia).

Definition Coproducts := ∏ (a : I -> C), Coproduct a.
Definition hasCoproducts :=  ∏ (a : I -> C), ∥ Coproduct a ∥.

Definition CoproductObject {a : I -> C} (CC : Coproduct a) : C := pr1 (pr1 CC).
Coercion CoproductObject : Coproduct >-> ob.

Definition CoproductIn {a : I -> C} (CC : Coproduct a): ∏ i, a i --> CoproductObject CC :=
  pr2 (pr1 CC).

Definition isCoproduct_Coproduct {a : I -> C} (CC : Coproduct a) :
   isCoproduct a (CoproductObject CC) (CoproductIn CC).
Proof.
  exact (pr2 CC).
Defined.

Definition CoproductArrow {a : I -> C} (CC : Coproduct a) {c : C} (f : ∏ i, a i --> c) :
      CoproductObject CC --> c.
Proof.
  exact (pr1 (pr1 (isCoproduct_Coproduct CC _ f))).
Defined.

Lemma CoproductInCommutes (a : I -> C) (CC : Coproduct a) :
     ∏ (c : C) (f : ∏ i, a i --> c) i, CoproductIn CC i · CoproductArrow CC f = f i.
Proof.
  intros c f i.
  exact (pr2 (pr1 (isCoproduct_Coproduct CC _ f)) i).
Qed.

Lemma CoproductIn_idtoiso {i1 i2 : I} (a : I -> C) (CC : Coproduct a)
      (e : i1 = i2) :
  idtoiso (maponpaths a e) · CoproductIn CC i2 = CoproductIn CC i1.
Proof.
  induction e.
  apply id_left.
Qed.

Lemma CoproductArrowUnique (a : I -> C) (CC : Coproduct a) (x : C)
    (f : ∏ i, a i --> x) (k : CoproductObject CC --> x)
    (Hk : ∏ i, CoproductIn CC i · k = f i) :
  k = CoproductArrow CC f.
Proof.
  set (H' := pr2 (isCoproduct_Coproduct CC _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Lemma CoproductArrowEta (a : I -> C) (CC : Coproduct a) (x : C)
    (f : CoproductObject CC --> x) :
    f = CoproductArrow CC (λ i, CoproductIn CC i · f).
Proof.
  now apply CoproductArrowUnique.
Qed.

Proposition CoproductArrow_eq
            {d : I → C}
            (z : C)
            (x : Coproduct d)
            (f g : x --> z)
            (p : ∏ (i : I), CoproductIn x i · f = CoproductIn x i · g)
  : f = g.
Proof.
  refine (CoproductArrowEta _ _ _ _ @ _ @ !(CoproductArrowEta _ _ _ _)).
  apply maponpaths.
  use funextsec.
  exact p.
Qed.

Definition CoproductOfArrows {a : I -> C} (CCab : Coproduct a) {c : I -> C}
    (CCcd : Coproduct c) (f : ∏ i, a i --> c i) :
          CoproductObject CCab --> CoproductObject CCcd :=
    CoproductArrow CCab (λ i, f i · CoproductIn CCcd i).

Lemma CoproductOfArrowsIn {a : I -> C} (CCab : Coproduct a) {c : I -> C}
    (CCcd : Coproduct c) (f : ∏ i, a i --> c i) :
    ∏ i, CoproductIn CCab i · CoproductOfArrows CCab CCcd f = f i · CoproductIn CCcd i.
Proof.
  unfold CoproductOfArrows; intro i.
  apply CoproductInCommutes.
Qed.

Definition make_Coproduct (a : I -> C) (c : C) (f : ∏ i, a i --> c) :
   isCoproduct _ _ f → Coproduct a.
Proof.
intro H.
use tpair.
- apply (tpair _ c f).
- apply H.
Defined.

Definition make_isCoproduct (hsC : has_homsets C) (a : I -> C) (co : C)
  (f : ∏ i, a i --> co) : (∏ (c : C) (g : ∏ i, a i --> c),
                                  ∃! k : C ⟦co, c⟧, ∏ i, f i · k = g i)
   → isCoproduct a co f.
Proof.
  intros H c cc.
  apply H.
Defined.

Lemma precompWithCoproductArrow {a : I -> C} (CCab : Coproduct a) {c : I -> C}
    (CCcd : Coproduct c) (f : ∏ i, a i --> c i)
    {x : C} (k : ∏ i, c i --> x) :
        CoproductOfArrows CCab CCcd f · CoproductArrow CCcd k =
         CoproductArrow CCab (λ i, f i · k i).
Proof.
apply CoproductArrowUnique; intro i.
now rewrite assoc, CoproductOfArrowsIn, <- assoc, CoproductInCommutes.
Qed.

Lemma postcompWithCoproductArrow {a : I -> C} (CCab : Coproduct a) {c : C}
    (f : ∏ i, a i --> c) {x : C} (k : c --> x)  :
       CoproductArrow CCab f · k = CoproductArrow CCab (λ i, f i · k).
Proof.
apply CoproductArrowUnique; intro i.
now rewrite assoc, CoproductInCommutes.
Qed.

Lemma Coproduct_endo_is_identity (a : I -> C) (CC : Coproduct a)
  (k : CoproductObject CC --> CoproductObject CC)
  (H1 : ∏ i, CoproductIn CC i · k = CoproductIn CC i)
  : identity _ = k.
Proof.
apply pathsinv0.
eapply pathscomp0; [apply CoproductArrowEta|].
apply pathsinv0, CoproductArrowUnique; intro i; apply pathsinv0.
now rewrite id_right, H1.
Qed.

End coproduct_def.

Section Coproducts.

Context (I : UU) (C : category) (CC : Coproducts I C).

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

End Coproducts.

Section functors.

Definition coproduct_functor_data (I : UU) {C : category}
  (PC : Coproducts I C) : functor_data (power_category I C) C.
Proof.
use tpair.
- intros p.
  apply (CoproductObject _ _ (PC p)).
- simpl; intros p q f.
  apply (CoproductOfArrows _ _ _ _ f).
Defined.

(** * The coproduct functor: C^I -> C *)
Definition coproduct_functor (I : UU) {C : category}
  (PC : Coproducts I C) : functor (power_category I C) C.
Proof.
apply (tpair _ (coproduct_functor_data _ PC)).
abstract (split;
          [intro x; simpl; apply pathsinv0, Coproduct_endo_is_identity;
           now intro i; rewrite CoproductOfArrowsIn, id_left
          | now intros x y z f g; simpl; rewrite CoproductOfArrows_comp]).
Defined.

End functors.

(* The coproduct of a family of functors *)
(* This is the old and not so good definition as it is unnecessarily complicated, also the proof
   that it is omega-cocontinuous requires that C has products *)
Definition coproduct_of_functors_alt_old (I : UU) {C D : category}
  (HD : Coproducts I D) (F : I -> functor C D) : functor C D :=
  functor_composite (delta_functor I C)
     (functor_composite (family_functor _ F)
                        (coproduct_functor _ HD)).

(** The coproduct of a family of functors *)
Definition coproduct_of_functors_alt (I : UU) {C D : category}
  (HD : Coproducts I D) (F : ∏ (i : I), functor C D)
  := functor_composite (tuple_functor F) (coproduct_functor _ HD).


(** * Coproducts lift to functor categories *)
Section def_functor_pointwise_coprod.

Context (I : UU) (C D : category) (HD : Coproducts I D).

Section coproduct_of_functors.

Context (F : I -> functor C D).

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
now apply (functor_eq _ _ D).
Qed.

Lemma coproduct_of_functors_alt_eq_coproduct_of_functors :
  coproduct_of_functors_alt _ HD F = coproduct_of_functors.
Proof.
now apply (functor_eq _ _ D).
Qed.

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

Context (A : functor C D) (f : ∏ i, nat_trans (F i) A).

Definition coproduct_nat_trans_data c : coproduct_of_functors c --> A c
  := CoproductArrow _ _ _ (λ i, f i c).

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
  : Coproduct I [C, D] F.
Proof.
use make_Coproduct.
- apply coproduct_of_functors.
- apply coproduct_nat_trans_in.
- use make_isCoproduct.
  + apply functor_category_has_homsets.
  + intros A f.
    use tpair.
    * apply (tpair _ (coproduct_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq D); intro c;
                apply (CoproductInCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypePath; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans D)|];
        apply (nat_trans_eq D); intro c;
        apply CoproductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End coproduct_of_functors.

Definition Coproducts_functor_precat : Coproducts I [C, D].
Proof.
  intros F.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.

(** * Coproducts from colimits *)
Section coproducts_from_colimits.

Context (I : UU) (C : category).

Definition I_graph : graph := (I,,λ _ _,empty).

Definition coproducts_diagram (F : I → C) : diagram I_graph C.
Proof.
exists F.
abstract (intros u v e; induction e).
Defined.

Definition Coproducts_cocone c (F : I → C) (H : ∏ i, F i --> c) :
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
use make_Coproduct.
+ apply (colim HF).
+ intros i; apply (colimIn HF).
+ apply (make_isCoproduct _ _ C); intros c Fic.
  use unique_exists.
  - now apply colimArrow, Coproducts_cocone.
  - abstract (simpl; intro i; apply (colimArrowCommutes HF)).
  - abstract (intros y; apply impred; intro i; apply C).
  - abstract (intros f Hf; apply colimArrowUnique; simpl in *; intros i; apply Hf).
Defined.

End coproducts_from_colimits.

Section DistributionThroughFunctor.

  Context {I : UU} {C D : category}
    (CPC : Coproducts I C) (CPD : Coproducts I D) (F : functor C D).

  Definition coprod_antidistributor (cs : power_category I C):
    CPD (fun i => F (cs i)) --> F (CPC cs).
  Proof.
    use CoproductArrow; intro i; apply (#F). apply CoproductIn.
  Defined.

  Lemma coprod_antidistributor_nat (cs1 cs2 : power_category I C) (g : power_category I C ⟦ cs1, cs2 ⟧) :
    coprod_antidistributor cs1 · #F (#(coproduct_functor I CPC) g) =
    #(coproduct_functor I CPD) (#(family_functor I (fun _ => F)) g) · coprod_antidistributor cs2.
  Proof.
    etrans.
    { apply postcompWithCoproductArrow. }
    etrans.
    2: { apply pathsinv0, precompWithCoproductArrow. }
    apply maponpaths.
    apply funextsec; intro i.
    etrans.
    { apply pathsinv0, functor_comp. }
    etrans.
    2: { cbn. apply functor_comp. }
    apply maponpaths.
    apply CoproductInCommutes.
  Qed.

   (** axiomatize extra requirements *)

  Definition coprod_distributor_data : UU := ∏ (cs : power_category I C),
     F (CPC cs) --> CPD (fun i => F (cs i)).

  Identity Coercion coprod_distributor_data_funclass: coprod_distributor_data >-> Funclass.

  Definition coprod_distributor_iso_law (δ : coprod_distributor_data) : UU :=
    ∏ (cs : power_category I C), is_inverse_in_precat (δ cs) (coprod_antidistributor cs).

  Definition coprod_distributor : UU := ∑ δ : coprod_distributor_data, coprod_distributor_iso_law δ.

  Definition coprod_distributor_to_data (δ : coprod_distributor) : coprod_distributor_data := pr1 δ.
  Coercion coprod_distributor_to_data : coprod_distributor >-> coprod_distributor_data.

End DistributionThroughFunctor.

Section DistributionForPrecompositionFunctor.

  Context {I : UU} {A B C : category} (CPC : Coproducts I C) (H : functor A B).

  Let CPAC : Coproducts I [A,C] := Coproducts_functor_precat I A C CPC.
  Let CPBC : Coproducts I [B,C] := Coproducts_functor_precat I B C CPC.
  Let precomp : functor [B,C] [A,C] := pre_composition_functor A B C H.

  Definition precomp_coprod_distributor_data : coprod_distributor_data CPBC CPAC precomp.
  Proof.
    intro Gs.
    apply nat_trans_id.
  Defined.

  Lemma precomp_coprod_distributor_law :
    coprod_distributor_iso_law _ _ _ precomp_coprod_distributor_data.
  Proof.
    intros Gs.
    split.
    - apply (nat_trans_eq C).
      intro c.
      cbn.
      rewrite id_left.
      apply pathsinv0, Coproduct_endo_is_identity.
      intro i.
      unfold coproduct_nat_trans_data.
      cbn in Gs.
      apply (CoproductInCommutes I C (λ i0 : I, Gs i0 (H c)) (CPC _) _
               (λ i0 : I, coproduct_nat_trans_in_data I B C CPC Gs i0 (H c)) i).
    - etrans.
      { apply postcompWithCoproductArrow. }
      etrans.
      2: { apply pathsinv0, CoproductArrowEta. }
      apply maponpaths; apply funextsec; intro i;
        (rewrite id_right; apply (nat_trans_eq C); intro c; apply id_right).
  Qed.

  Definition precomp_coprod_distributor : coprod_distributor CPBC CPAC precomp :=
    _,,precomp_coprod_distributor_law.

End DistributionForPrecompositionFunctor.

(**
 Coproducts are unique
 *)
Definition eq_Coproduct
           {C : category}
           {J : UU}
           {D : J → C}
           (coprod₁ coprod₂ : Coproduct J C D)
           (q : CoproductObject _ _ coprod₁ = CoproductObject _ _ coprod₂)
           (e : ∏ (j : J),
                CoproductIn _ _ coprod₁ j
                =
                CoproductIn _ _ coprod₂ j · idtoiso (!q))
  : coprod₁ = coprod₂.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    use isapropiscontr.
  }
  use total2_paths_f.
  - exact q.
  - rewrite transportf_sec_constant.
    use funextsec.
    intro j.
    rewrite <- !idtoiso_postcompose.
    pose (p := e j).
    rewrite !idtoiso_inv in p.
    refine (maponpaths (λ z, z · _) p @ _).
    rewrite !assoc'.
    refine (_ @  id_right _).
    apply maponpaths.
    apply z_iso_after_z_iso_inv.
Qed.

Definition z_iso_between_Coproduct
           {C : category}
           {J : UU}
           {D : J → C}
           (coprod₁ coprod₂ : Coproduct J C D)
  : z_iso coprod₁ coprod₂.
Proof.
  use make_z_iso.
  - exact (CoproductArrow _ _ coprod₁ (CoproductIn _ _ coprod₂)).
  - exact (CoproductArrow _ _ coprod₂ (CoproductIn _ _ coprod₁)).
  - split.
    + abstract
        (use CoproductArrow_eq ;
         intro j ;
         rewrite !assoc ;
         rewrite !CoproductInCommutes ;
         rewrite id_right ;
         apply idpath).
    + abstract
        (use CoproductArrow_eq ;
         intro j ;
         rewrite !assoc ;
         rewrite !CoproductInCommutes ;
         rewrite id_right ;
         apply idpath).
Defined.

Definition isaprop_Coproduct
           {C : category}
           (HC : is_univalent C)
           (J : UU)
           (D : J → C)
  : isaprop (Coproduct J C D).
Proof.
  use invproofirrelevance.
  intros p₁ p₂.
  use eq_Coproduct.
  - refine (isotoid _ HC _).
    apply z_iso_between_Coproduct.
  - intro j.
    rewrite idtoiso_inv.
    rewrite idtoiso_isotoid ; cbn.
    rewrite CoproductInCommutes.
    apply idpath.
Qed.

Section Coproduct_different_indexers.


Definition CoproductOfArrowsInclusion {I J : UU} {C : category}
    (incl : I -> J) {a : I -> C} (CCab : Coproduct _ _ a) {c : J -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c (incl i)) :
          CoproductObject _ _ CCab --> CoproductObject _ _ CCcd :=
  CoproductArrow _ _ CCab (λ i, f i · CoproductIn _ _ CCcd (incl i)).


(* non-implicit I/C for backwards compatibility *)
Definition CoproductOfArrows' (I : UU) (C : category)
    {a : I -> C} (CCab : Coproduct _ _ a) {c : I -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c i) :
        CoproductObject _ _ CCab --> CoproductObject _ _ CCcd :=
  CoproductOfArrowsInclusion (idfun I) CCab CCcd f.

Lemma CoproductOfArrowsInclusionIn {I J : UU} {C : category}
    (incl : I -> J) {a : I -> C} (CCab : Coproduct _ _ a) {c : J -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c (incl i)) :
  ∏ i, CoproductIn _ _ CCab i · CoproductOfArrowsInclusion incl CCab CCcd f = f i · CoproductIn _ _ CCcd (incl i).
Proof.
  unfold CoproductOfArrows; intro i.
  apply CoproductInCommutes.
Qed.

(* non-implicit I/C for backwards compatibility *)
Lemma CoproductOfArrows'In (I : UU) (C : category)
    {a : I -> C} (CCab : Coproduct _ _ a) {c : I -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c i) :
  ∏ i, CoproductIn _ _ CCab i · CoproductOfArrows' _ _ CCab CCcd f = f i · CoproductIn _ _ CCcd i.
Proof.
  apply CoproductOfArrowsInclusionIn.
Qed.

Lemma precompWithCoproductArrowInclusion {I J : UU} {C : category}
  (incl : I -> J) {a : I -> C} (CCab : Coproduct _ _ a) {c : J -> C}
  (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c (incl i))
  {x : C} (k : ∏ i, c i --> x) :
      CoproductOfArrowsInclusion incl CCab CCcd f · CoproductArrow _ _ CCcd k =
       CoproductArrow _ _ CCab (λ i, f i · k (incl i)).
Proof.
  apply CoproductArrowUnique; intro i.
  now rewrite assoc, CoproductOfArrowsInclusionIn, <- assoc, CoproductInCommutes.
Qed.

(* non-implicit I/C for backwards compatibility *)
Lemma precompWithCoproductArrow' (I : UU) (C : category)
  {a : I -> C} (CCab : Coproduct _ _ a) {c : I -> C}
  (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c i)
  {x : C} (k : ∏ i, c i --> x) :
      CoproductOfArrows' _ _ CCab CCcd f · CoproductArrow _ _ CCcd k =
       CoproductArrow _ _ CCab (λ i, f i · k i).
Proof.
  apply precompWithCoproductArrowInclusion.
Qed.

Definition CoproductOfArrowsInclusion_comp {I J K: UU} {C : category}
    {a : I -> C} {b : J -> C} {c : K -> C}
    (CCI : Coproducts I C) (CCJ : Coproducts J C) (CCK : Coproducts K C)
    {inclI : I -> J} {inclJ : J -> K}
    (f : ∏ i, a i --> b (inclI i)) (g : ∏ j, b j --> c (inclJ j)) :
    CoproductOfArrowsInclusion inclI (CCI _) (CCJ _) f ·
        CoproductOfArrowsInclusion inclJ (CCJ _) (CCK _) g
    = CoproductOfArrowsInclusion (λ i, inclJ (inclI i)) (CCI _) (CCK _) (λ i, f i · g (inclI i)).
Proof.
  apply CoproductArrowUnique; intro i.
  rewrite assoc, CoproductOfArrowsInclusionIn.
  now rewrite <- assoc, CoproductOfArrowsInclusionIn, assoc.
Qed.

(* non-implicit I/C for backwards compatibility *)
Definition CoproductOfArrows'_comp (I : UU) (C : category) (CC : Coproducts I C)
  (a b c : I -> C) (f : ∏ i, a i --> b i) (g : ∏ i, b i --> c i) :
   CoproductOfArrows' _ _ _ _ f · CoproductOfArrows' _ _ (CC _) (CC _) g
   = CoproductOfArrows' _ _ (CC _) (CC _)(λ i, f i · g i).
Proof.
  apply CoproductOfArrowsInclusion_comp.
Qed.

End Coproduct_different_indexers.
