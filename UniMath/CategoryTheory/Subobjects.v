(** *************************************************************************

Definition and theory about subobjects of an object c

Contents:

- Category of subobjects (monos) of c ([Subobjectscategory])
- Set of subobjects as equivalence classes of monos ([SubObj])
- Proof that the set of subobjects of an object is a poset ([SubObjPoset])

Written by: Tomi Pannila and Anders Mörtberg, 2016-2017

*****************************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Local Open Scope cat.

(** * Definition of the category of subobjects (monos) of c *)
Section def_subobjects.

  Context {C : precategory} (hsC : has_homsets C).

  Definition Subobjectscategory (c : C) : precategory :=
    slice_precat (subprecategory_of_monics C hsC)
                 (subprecategory_of_monics_ob C hsC c)
                 (has_homsets_subprecategory_of_monics C hsC).

  Lemma has_homsets_Subobjectscategory (c : C) :
    has_homsets (Subobjectscategory c).
  Proof.
  apply has_homsets_slice_precat.
  Qed.

  (** Construction of a subobject from a monic *)
  Definition Subobjectscategory_ob {c c' : C} (h : C⟦c', c⟧) (isM : isMonic h) :
    Subobjectscategory c := (subprecategory_of_monics_ob C hsC c',,(h,,isM)).

  (** Given any subobject S of c and a morphism h : c' -> c, by taking then pullback of S by h we
      obtain a subobject of c'. *)
  Definition PullbackSubobject (PB : Pullbacks C) {c : C} (S : Subobjectscategory c) {c' : C} (h : C⟦c', c⟧) :
    Subobjectscategory c'.
  Proof.
    set (pb := PB _ _ _ h (pr1 (pr2 S))).
    use Subobjectscategory_ob.
    - exact pb.
    - exact (PullbackPr1 pb).
    - use MonicPullbackisMonic'.
  Defined.

End def_subobjects.

(** * Definition of subobjects as equivalence classes of monos *)
Section subobj.

Context {C : precategory} (hsC : has_homsets C).

(** Equivalence classes of subobjects defined by identifying monos into c
    with isomorphic source *)
Definition SubObj (c : C) : HSET :=
  hSetpair (setquot (iso_eqrel (Subobjectscategory hsC c))) (isasetsetquot _).

(* For f and g monics into c: f <= g := ∃ h, f = h · g *)
Definition monorel c : hrel (Subobjectscategory hsC c) :=
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

Lemma are_isomorphic_monorel {c : C} {x1 y1 x2 y2 : Subobjectscategory hsC c}
  (h1 : are_isomorphic _ x1 y1) (h2 : are_isomorphic _ x2 y2) :
  monorel c x1 x2 → monorel c y1 y2.
Proof.
apply hinhuniv; intros f.
change (ishinh_UU (iso x1 y1)) in h1.
change (ishinh_UU (iso x2 y2)) in h2.
apply h1; clear h1; intro h1.
apply h2; clear h2; intro h2.
intros P H; apply H; clear P H.
set (h1_inv := inv_from_iso h1).
set (Hh1 := iso_after_iso_inv h1).
exists (pr1 (pr1 h1_inv) · pr1 f · pr1 (pr1 (pr1 h2))).
set (Htemp := maponpaths pr1 (pr2 (pr1 h2))).
apply pathsinv0; simpl in *.
rewrite <-!assoc, <- Htemp.
intermediate_path (pr1 (pr1 h1_inv) · pr1 (pr2 x1)).
{ apply maponpaths, pathsinv0, (pr2 f). }
etrans; [ apply maponpaths, (maponpaths pr1 (pr2 (pr1 h1))) |]; simpl.
rewrite assoc.
etrans; [ eapply cancel_postcomposition, (maponpaths pr1 (maponpaths pr1 Hh1)) |].
apply id_left.
Qed.

(** Construct a quotient relation on the Subobjects from the relation on monos *)
Definition SubObj_rel (c : C) : hrel (pr1 (SubObj c)).
Proof.
use quotrel.
- apply monorel.
- intros x1 y1 x2 y2 h1 h2.
  apply hPropUnivalence.
  + apply (are_isomorphic_monorel h1 h2).
  + apply (are_isomorphic_monorel (eqrelsymm (iso_eqrel _) _ _ h1)
                                  (eqrelsymm (iso_eqrel _) _ _ h2)).
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
assert (int : ∏ x1 x2, isaprop (SubObj_rel c x1 x2 → SubObj_rel c x2 x1 -> x1 = x2)).
{ intros x1 x2.
  repeat (apply impred; intro).
  apply (isasetsetquot _ x1 x2).
}
apply (setquotuniv2prop _ (λ x1 x2, hProppair _ (int x1 x2))).
intros x y h1 h2.
simpl in *. (* This is slow *)
apply (iscompsetquotpr (iso_eqrel (Subobjectscategory hsC c))).
generalize h1; clear h1; apply hinhuniv; intros [h1 Hh1].
generalize h2; clear h2; apply hinhuniv; intros [h2 Hh2].
apply hinhpr, (invmap (iso_weq _ (subprecategory_of_monics_ob C hsC c) _ _)).
induction x as [[x []] [fx Hfx]].
induction y as [[y []] [fy Hfy]].
simpl in *.
assert (mon_h1 : isMonic h1).
{ apply (isMonic_postcomp _ h1 fy); rewrite <- Hh1; apply Hfx. }
assert (mon_h2 : isMonic h2).
{ apply (isMonic_postcomp _ h2 fx); rewrite <- Hh2; apply Hfy. }
use tpair.
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

End subobj.
