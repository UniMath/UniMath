(** * Subobjects *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Local Open Scope cat.

(** * Definition of subobjects *)
Section def_subobjects.

  Context {C : precategory} (hsC : has_homsets C).

  Definition SubobjectsPrecategory (c : C) : precategory :=
    slice_precat (subprecategory_of_monics C hsC)
                 (subprecategory_of_monics_ob C hsC c)
                 (has_homsets_subprecategory_of_monics C hsC).

  Lemma has_homsets_SubobjectsPrecategory (c : C) :
    has_homsets (SubobjectsPrecategory c).
  Proof.
  apply has_homsets_slice_precat.
  Qed.

  (** Construction of a subobject from a monic *)
  Definition SubobjectsPrecategory_ob {c c' : C} (h : C⟦c', c⟧) (isM : isMonic h) :
    SubobjectsPrecategory c := (subprecategory_of_monics_ob C hsC c',,(h,,isM)).

  (** Given any subobject S of c and a morphism h : c' -> c, by taking then pullback of S by h we
      obtain a subobject of c'. *)
  Definition PullbackSubobject (PB : Pullbacks C) {c : C} (S : SubobjectsPrecategory c) {c' : C} (h : C⟦c', c⟧) :
    SubobjectsPrecategory c'.
  Proof.
    set (pb := PB _ _ _ h (pr1 (pr2 S))).
    use SubobjectsPrecategory_ob.
    - exact pb.
    - exact (PullbackPr1 pb).
    - use MonicPullbackisMonic'.
  Defined.

End def_subobjects.

Section iso_rel.

Context (C : precategory).

(** a and b are related if there merely exists an iso between them *)
Definition iso_rel : hrel C := λ a b, ∥iso a b∥.

Lemma iseqrel_iso_rel : iseqrel iso_rel.
Proof.
repeat split.
- intros x y z h1.
  apply hinhuniv; intros h2; generalize h1; clear h1.
  now apply hinhuniv; intros h1; apply hinhpr, (iso_comp h1 h2).
- now intros x; apply hinhpr, identity_iso.
- now intros x y; apply hinhuniv; intro h1; apply hinhpr, iso_inv_from_iso.
Qed.

Definition iso_eqrel : eqrel C := (iso_rel,,iseqrel_iso_rel).

End iso_rel.

Section subobj.

Context {C : precategory} (hsC : has_homsets C).

(** Equivalence classes of subobjects defined by identifying monos into c
    with isomorphic source *)
Definition SubObj (c : C) : HSET :=
  hSetpair (setquot (iso_eqrel (SubobjectsPrecategory hsC c))) (isasetsetquot _).

(* For f and g monics into c: f <= g := exists h, f = h ;; g *)
Definition monorel c : hrel (SubobjectsPrecategory hsC c) :=
  λ f g, ∃ h, pr1 (pr2 f) = h · pr1 (pr2 g).

Lemma isrefl_monorel (c : C) : isrefl (monorel c).
Proof.
intros x; apply hinhpr.
exists (pr1 (pr1 (identity x))).
now rewrite id_left.
Qed.

Lemma istrans_monorel (c : C) : istrans (monorel c).
Proof.
intros x y z h1.
apply hinhuniv; intros h2; generalize h1; clear h1.
apply hinhuniv; intros h1; apply hinhpr.
exists (pr1 h1 · pr1 h2).
now rewrite <- assoc, <- (pr2 h2), <- (pr2 h1).
Qed.

Lemma ispreorder_monorel c : ispreorder (monorel c).
Proof.
exact (istrans_monorel c,,isrefl_monorel c).
Qed.

Lemma iso_monorel {c : C} {x1 y1 x2 y2 : SubobjectsPrecategory hsC c}
  (h1 : iso_rel _ x1 y1) (h2 : iso_rel _ x2 y2) :
  monorel c x1 x2 → monorel c y1 y2.
Proof.
apply hinhuniv.
intros [f Hf].
apply h1; clear h1; intro h1.
apply h2; clear h2; intro h2.
intros P H; apply H; clear P H.
set (h1_inv := inv_from_iso h1).
set (Hh1 := @iso_after_iso_inv (slice_precat (subprecategory_of_monics C hsC)
             (subprecategory_of_monics_ob C hsC c) (has_homsets_subprecategory_of_monics C hsC)) _ _ h1).
destruct x1 as [[x1 []] [f1 Hf1]].

destruct x2 as [[x3 []] [f3 Hf3]].
destruct y1 as [[x2 []] [f2 Hf2]].
destruct y2 as [[x4 []] [f4 Hf4]].
destruct h1 as [[[H1 H2] H3] H4].
destruct h2 as [[[G1 G2] G3] G4].
simpl in *.
exists (pr1 (pr1 h1_inv) · f · G1).
set (XX := maponpaths pr1 G3).
simpl in *.
rewrite <-!assoc, <- XX, <- Hf.
set (X := maponpaths pr1 H3).
simpl in *.
apply pathsinv0.
etrans.
eapply maponpaths.
apply X.
rewrite assoc.
etrans.
eapply cancel_postcomposition.
set (mooooo := maponpaths pr1 (maponpaths pr1 Hh1)).
apply mooooo.
apply id_left.
Qed.

Definition SubObj_rel (c : C) : hrel (pr1 (SubObj c)).
Proof.
use quotrel.
- apply monorel.
(* use (setquotuniv2 (iso_rel _) (_,,isasethProp) (monorel c)). *)
- intros x1 y1 x2 y2 h1 h2.
apply hPropUnivalence.
+ apply (iso_monorel h1 h2).
+ apply (iso_monorel (eqrelsymm (iso_eqrel _) _ _ h1) (eqrelsymm (iso_eqrel _) _ _ h2)).
Defined.

Lemma istrans_SubObj_rel (c : C) : istrans (SubObj_rel c).
Proof.
apply istransquotrel, istrans_monorel.
Qed.

Lemma isrefl_SubObj_rel (c : C) : isrefl (SubObj_rel c).
Proof.
apply isreflquotrel, isrefl_monorel.
Qed.

Lemma ispreorder_SubObj_rel (c : C) : ispreorder (SubObj_rel c).
Proof.
exact (istrans_SubObj_rel c,,isrefl_SubObj_rel c).
Qed.

Lemma isantisymm_SubObj_rel (c : C) : isantisymm (SubObj_rel c).
Proof.
unfold isantisymm; simpl.
assert (int : ∏ (x1 x2 : setquot (iso_eqrel (SubobjectsPrecategory hsC c))),
              isaprop (SubObj_rel c x1 x2 → SubObj_rel c x2 x1 -> x1 = x2)).
{ intros x1 x2.
  repeat (apply impred; intro).
  apply (isasetsetquot _ x1 x2).
}
apply (setquotuniv2prop _ (λ x1 x2, hProppair _ (int x1 x2))).
intros x y h1 h2; simpl in *.
apply (iscompsetquotpr (iso_eqrel (SubobjectsPrecategory hsC c))).
generalize h1; clear h1; apply hinhuniv; intros [h1 Hh1].
generalize h2; clear h2; apply hinhuniv; intros [h2 Hh2].
apply hinhpr.
apply (invmap (iso_weq _ (subprecategory_of_monics_ob C hsC c) _ _)).
destruct x as [[x []] [fx Hfx]].
destruct y as [[y []] [fy Hfy]].
simpl in *.
assert (mon_h1 : isMonic h1).
{ apply (isMonic_postcomp _ h1 fy); rewrite <- Hh1; apply Hfx. }
assert (mon_h2 : isMonic h2).
{ apply (isMonic_postcomp _ h2 fx); rewrite <- Hh2; apply Hfy. }
mkpair.
- exists (h1,,mon_h1).
  apply (@is_iso_from_is_z_iso (subprecategory_of_monics C hsC)).
  exists (h2,,mon_h2).
  split; apply subtypeEquality; try (intros xx; apply isapropisMonic, hsC).
  + simpl; apply Hfx.
    now rewrite <- assoc, <- Hh2, <- Hh1, id_left.
  + simpl; apply Hfy.
    now rewrite <- assoc, <- Hh1, <- Hh2, id_left.
- apply subtypeEquality; simpl; try apply Hh1.
  now intros xx; apply isapropisMonic, hsC.
Qed.

Definition SubObjPoset (c : C) : Poset :=
  (SubObj c,,SubObj_rel c,,ispreorder_SubObj_rel c,,isantisymm_SubObj_rel c).


(* Definition SubObj (c : C) : UU := ∥ ∑ (af : ∑ (a : C), C⟦a,c⟧), isMonic (pr2 af) ∥. *)

(* a is a subobject of c *)
(* Definition SubObj (a c : C) : UU := ∥ ∑ (f : C⟦a,c⟧), isMonic f ∥. (* Monic C a c. *) *)

(* Definition SubObjects (c : C) : UU := ∑ (a : ob C), SubObj a c. *)

(* Definition SubObj (c : C) : hsubtype (∑ a, precategory_morphisms a c). *)
(* Proof. *)
(*   intros f. *)
(*   exists (isMonic (pr2 f)). *)
(*   apply isapropisMonic, hsC. *)
(* (* apply (hProppair (∥ Monic C a c ∥) (isapropishinh _)). *) *)
(* Defined. *)

End subobj.
