(** *************************************************************************

Definition and theory about subobjects of an object c

Contents:

- Category of subobjects (monos) of c ([Subobjectscategory])
- Set of subobjects as equivalence classes of monos ([SubObj])
- Proof that the set of subobjects of an object is a poset ([SubObjPoset])
- The definition of the functor from C^op to hset_category
	which maps c to the set of the subobject (module z_isomorphism) of c
	and maps morphism "by pullback" ([SubObj_Functor])

Written by: Tomi Pannila and Anders Mörtberg, 2016-2017

*****************************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.

(** * Definition of the category of subobjects (monos) of c *)
Section def_subobjects.

  Context {C : category}.

  Definition Subobjectscategory (c : C) : category :=
    slice_cat (subcategory_of_monics C)
                 (subprecategory_of_monics_ob C c).

  Lemma is_univalent_Subobjectscategory
    (H : is_univalent C)
    (c : C)
    : is_univalent (Subobjectscategory c).
  Proof.
    apply is_univalent_slicecat.
    apply is_univalent_monics_cat.
    exact H.
  Qed.

  (** Construction of a subobject from a monic *)
  Definition Subobjectscategory_ob {c c' : C} (h : C⟦c', c⟧) (isM : isMonic h) :
    Subobjectscategory c := (subprecategory_of_monics_ob C c',,(h,,isM)).

  (** Accessor for an object of Subobjectscategory*)
  Section obAccessor.

  Context {c:C} (S : Subobjectscategory c).

  Definition Subobject_dom : C := pr1 (pr1 S).
  Definition Subobject_Monic := pr2 S.
  Definition Subobject_mor : C⟦ Subobject_dom , c ⟧ := pr1 (pr2 S).
  Definition Subobject_isM : isMonic(Subobject_mor) := pr2 (pr2 S).

  End obAccessor.

  (** Accessor for a morphism of Subobjectscategory*)
  Section morAccessor.

  Context {c:C} {S S' : Subobjectscategory c} (h : S --> S').


  Definition Subobjectmor_Cmor : C⟦ Subobject_dom S, Subobject_dom S' ⟧ := pr1 (pr1 h).
  Definition Subobjectmor_isM : isMonic(Subobjectmor_Cmor) := pr2 (pr1 h).
  Definition Subobjectmor_tri := maponpaths (pr1) (pr2 h).

  End morAccessor.

  (** Given any subobject S of c and a morphism h : c' -> c, by taking then pullback of S by h we
      obtain a subobject of c'. *)
  Definition PullbackSubobject (PB : Pullbacks C) {c : C} (S : Subobjectscategory c) {c' : C} (h : C⟦c', c⟧) :
    Subobjectscategory c'.
  Proof.
    set (pb := PB _ _ _ h (Subobject_mor S)).
    use Subobjectscategory_ob.
    - exact pb.
    - exact (PullbackPr1 pb).
    - use MonicPullbackisMonic'.
  Defined.

  (*a z_iso in Subobjectscategory can be obtained by
  a z_iso on the underlying category C which makes the triangle commute*)
  Definition make_z_iso_in_Subobjectscategory {c : C} {S S' : Subobjectscategory c}
  (h : C ⟦Subobject_dom S ,Subobject_dom S'⟧)
  (is_z_iso : is_z_isomorphism h)
  (tri : Subobject_mor S = h · Subobject_mor S')
  : z_iso S S'.
  Proof.
    use make_z_iso'.
    + use tpair.
      - use precategory_morphisms_in_subcat.
        * exact h.
        * use is_iso_isMonic.
          exact is_z_iso.
      - use eq_in_sub_precategory.
        exact tri.
    + use z_iso_to_slice_precat_z_iso.
      use is_z_iso_in_subcategory_of_monics_weq.
      exact is_z_iso.
  Defined.

  (** a z_iso is Subobjectcategory gives, in particular, a z_iso of C between domains*)
  Definition z_iso_from_z_iso_in_Subobjectcategory {c : C}
  {S S' : Subobjectscategory c} (h : z_iso S S')
  : (z_iso (Subobject_dom S) (Subobject_dom S')).
  Proof.
    use make_z_iso.
    + exact (Subobjectmor_Cmor h).
    + exact (Subobjectmor_Cmor (inv_from_z_iso h)).
    + induction h as (h, (g,(hg,gh))).
      use make_is_inverse_in_precat.
      - exact (maponpaths Subobjectmor_Cmor hg).
      - exact (maponpaths Subobjectmor_Cmor gh).
  Defined.

End def_subobjects.

(** * Definition of subobjects as equivalence classes of monos *)
Section subobj.

Context {C : category}.

(** Equivalence classes of subobjects defined by identifying monos into c
    with isomorphic source *)
Definition SubObj (c : C) : hSet :=
  make_hSet (setquot (z_iso_eqrel (C:=Subobjectscategory c))) (isasetsetquot _).

Definition SubObj_iseqc {c:C} (S : SubObj c) := pr2 S.

Definition PullbackSubObj (PB : Pullbacks C) {c : C} (S : SubObj c)
  {c' : C} (h : C⟦c', c⟧)
  : SubObj c'.
Proof.
  use (setquotfun (z_iso_eqrel (C:=Subobjectscategory c))).
  + intro s.
    use (PullbackSubobject PB s h).
  + intros u v.
    use hinhfun.
    intro uv.
    use make_z_iso_in_Subobjectscategory.
    - use (iso_between_pullbacks
        (PullbackSqrCommutes (PB _ _ _ h (Subobject_mor u)))
        (PullbackSqrCommutes (PB _ _ _ h (Subobject_mor v)))
        (isPullback_Pullback (PB _ _ _ h (Subobject_mor u)))
        (isPullback_Pullback (PB _ _ _ h (Subobject_mor v)))
      ).
      * exact (identity_z_iso c').
      * use z_iso_from_z_iso_in_Subobjectcategory.
        exact uv.
      * exact (identity_z_iso c).
      * rewrite id_left, id_right.
        apply idpath.
      * rewrite id_right.
        apply pathsinv0.
        use Subobjectmor_tri.
    - use z_iso_is_z_isomorphism.
    - rewrite <-(id_right (Subobject_mor _)).
      use pathsinv0.
      use PullbackArrow_PullbackPr1.
  + exact S.
Defined.

(* For f and g monics into c: f <= g := ∃ h, f = h · g *)
Definition monorel (c : C) : hrel (Subobjectscategory c) :=
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

Lemma are_z_isomorphic_monorel {c : C} {x1 y1 x2 y2 : Subobjectscategory c}
  (h1 : are_z_isomorphic x1 y1) (h2 : are_z_isomorphic x2 y2) :
  monorel c x1 x2 → monorel c y1 y2.
Proof.
apply hinhuniv; intros f.
change (ishinh_UU (z_iso x1 y1)) in h1.
change (ishinh_UU (z_iso x2 y2)) in h2.
apply h1; clear h1; intro h1.
apply h2; clear h2; intro h2.
intros P H; apply H; clear P H.
set (h1_inv := inv_from_z_iso h1).
set (Hh1 := z_iso_after_z_iso_inv h1).
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
  + apply (are_z_isomorphic_monorel h1 h2).
  + apply (are_z_isomorphic_monorel (eqrelsymm (z_iso_eqrel) _ _ h1)
                                  (eqrelsymm (z_iso_eqrel) _ _ h2)).
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
apply (setquotuniv2prop _ (λ x1 x2, make_hProp _ (int x1 x2))).
intros x y h1 h2.
simpl in *. (* This is slow *)
apply (iscompsetquotpr (z_iso_eqrel (C:=Subobjectscategory c))).
generalize h1; clear h1; apply hinhuniv; intros [h1 Hh1].
generalize h2; clear h2; apply hinhuniv; intros [h2 Hh2].
apply hinhpr, (invmap (weq_z_iso _ (subprecategory_of_monics_ob C c) _ _)).
induction x as [[x []] [fx Hfx]].
induction y as [[y []] [fy Hfy]].
simpl in *.
assert (mon_h1 : isMonic h1).
{ apply (isMonic_postcomp _ h1 fy); rewrite <- Hh1; apply Hfx. }
assert (mon_h2 : isMonic h2).
{ apply (isMonic_postcomp _ h2 fx); rewrite <- Hh2; apply Hfy. }
use tpair.
- exists (h1,,mon_h1).
  exists (h2,,mon_h2).
  split; apply subtypePath.
  + intros xx. apply isapropisMonic.
  + simpl; apply Hfx.
    now rewrite <- assoc, <- Hh2, <- Hh1, id_left.
  + intros xx. apply isapropisMonic.
  + simpl; apply Hfy.
    now rewrite <- assoc, <- Hh1, <- Hh2, id_left.
- apply subtypePath; simpl; try apply Hh1.
  now intros xx; apply isapropisMonic.
Qed.

Definition SubObjPoset (c : C) : Poset :=
  (SubObj c,,SubObj_rel c,,ispreorder_SubObj_rel c,,isantisymm_SubObj_rel c).

End subobj.

(*Definition of the functor C^op -> HSET which maps c on SubObj c and maps morphism "by pullback"*)
Section SubObj_functor.

Context (C : category) (PB : Pullbacks C).

Definition SubObj_Functor_data : functor_data (op_cat C) hset_category.
Proof.
  use make_functor_data.
    + intro c.
      cbn in c.
      exact (SubObj c).
    + intros c c' f Sm.
      use PullbackSubObj.
      - exact PB.
      - exact c.
      - exact Sm.
      - exact f.
Defined.

Theorem SubObj_Functor_isfunctor : is_functor (SubObj_Functor_data).
Proof.
  split.
  + intro c.
    cbn in c.
    use funextfun.
    intro S.
    change (pr1hSet (SubObj c)) in S.
    use (squash_to_prop (X:=pr1setquot _ S)).
    { exact (eqax0 (SubObj_iseqc S)). }
    { use isasetsetquot. }
    intro m.
    induction (setquotl0 _ S m).
    cbn.
    use (weqpathsinsetquot (z_iso_eqrel (C:=Subobjectscategory c))).
    use hinhpr.
    use make_z_iso_in_Subobjectscategory.
    - use PullbackPr2.
    - use Pullback_of_z_iso'.
      exact (identity_is_z_iso c).
    - cbn.
      rewrite <- PullbackSqrCommutes, id_right.
      apply idpath.
  + intros c c' c'' f f'.
    cbn in c, c', c'', f, f'.
    use funextfun.
    intro S.
    use (squash_to_prop (X:=pr1setquot _ S)).
    { exact (eqax0 (SubObj_iseqc S)). }
    { use isasetsetquot. }
    intro m.
    induction (setquotl0 _ S m).
    use weqpathsinsetquot.
    use hinhpr.
    induction m as (m,Sm).
    cbn.
    set (pb := (PB _ _ _ f ((Subobject_mor m)))).
    set (pbpb := PB _ _ _ f' (PullbackPr1 pb)).
    transparent assert (pb_glued : (Pullback (f'·f) (Subobject_mor m))). {
      use make_Pullback.
      - exact pbpb.
      - exact (PullbackPr1 pbpb).
      - exact ((PullbackPr2 pbpb)·(PullbackPr2 pb)).
      - use glueSquares.
        * exact (PullbackPr1 pb).
        * use PullbackSqrCommutes.
        * use PullbackSqrCommutes.
      - use (isPullbackGluedSquare
          (isPullback_Pullback pb)
          (isPullback_Pullback pbpb)).
    }
    use make_z_iso_in_Subobjectscategory.
    - cbn.
      fold pb.
      fold pbpb.
      assert (H : PullbackObject pb_glued = PullbackObject pbpb). {
        apply idpath.
      }
      induction H.
      use z_iso_from_Pullback_to_Pullback.
    - use z_iso_is_z_isomorphism.
    - cbn.
      fold pb.
      fold pbpb.
      assert (H : PullbackPr1 pb_glued = PullbackPr1 pbpb). { apply idpath. }
      induction H.
      apply pathsinv0.
      use (PullbackArrow_PullbackPr1 pb_glued).
Defined.

Definition SubObj_Functor : C^op ⟶ hset_category.
Proof.
  use make_functor.
    + exact SubObj_Functor_data.
    + exact SubObj_Functor_isfunctor.
Defined.

End SubObj_functor.
