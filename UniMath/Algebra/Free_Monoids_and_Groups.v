(** Authors Floris van Doorn, December 2017 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Combinatorics.Lists.

(** ** Contents
- Free monoid on a set
- Free abelian monoid on a set
- Free group on a set
- Free abelian group on set
*)

Local Open Scope multmonoid_scope.
Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

(* Free monoid on a set *)
Lemma ismonoidop_concatenate (X : UU) : ismonoidop (@concatenate X).
Proof.
  use mk_ismonoidop.
  - use assoc_concatenate.
  - use isunitalpair.
    + exact [].
    + use isunitpair.
      * use nil_concatenate.
      * use concatenate_nil.
Defined.

Definition free_monoid (X : hSet) : monoid :=
  monoidpair (setwithbinoppair (hSetpair (list X) (isofhlevellist 0 (pr2 X))) _)
             (ismonoidop_concatenate X).

Definition free_monoid_unit {X : hSet} (x : X) : free_monoid X :=
  x::[].

Definition free_monoid_extend {X : hSet} {Y : monoid} (f : X → Y) : monoidfun (free_monoid X) Y.
Proof.
  use monoidfunconstr.
  - intro l. exact (iterop_list_mon (map f l)).
  - use mk_ismonoidfun.
    + intros l1 l2. refine (maponpaths _ (map_concatenate _ _ _) @ _).
      apply iterop_list_mon_concatenate.
    + reflexivity.
Defined.

Lemma free_monoid_extend_comp {X : hSet} {Y : monoid} (g : monoidfun (free_monoid X) Y):
  free_monoid_extend (g ∘ free_monoid_unit) ~ g.
Proof.
  unfold homot. simpl. apply list_ind.
    + exact (! monoidfununel g).
    + intros x xs IH. rewrite map_cons, iterop_list_mon_step, IH.
      exact (!pr1 (pr2 g) _ _).
Defined.

Definition isfree_free_monoid (X : hSet) (Y : monoid) : (X → Y) ≃ monoidfun (free_monoid X) Y.
Proof.
  use weq_iso.
  - apply free_monoid_extend.
  - intro g. exact (g ∘ free_monoid_unit).
  - intro f. apply funextfun. intro x. apply iterop_list_mon_singleton.
  - intro g. apply monoidfun_paths. apply funextfun. exact (free_monoid_extend_comp g).
Defined.

(* We don't use free_monoid_extend, so that the underlying function is map *)
Definition free_monoidfun {X Y : hSet} (f : X → Y) : monoidfun (free_monoid X) (free_monoid Y).
Proof.
  use monoidfunconstr.
  - intro l. exact (map f l).
  - use mk_ismonoidfun.
    + intros l1 l2. apply map_concatenate.
    + reflexivity.
Defined.

Definition reverse_binopfun (X : hSet) :
  binopfun (free_monoid X) (setwithbinop_rev (free_monoid X)).
Proof.
  use binopfunpair.
  - exact reverse.
  - intros x x'. apply reverse_concatenate.
Defined.

(* Free abelian monoid on a set *)

Definition free_abmonoid_hrel (X : hSet) : hrel (free_monoid X) :=
  λ g h, ∃ x y, x * y = g × y * x = h.

Lemma free_abmonoid_hrel_intro {X : hSet} (l1 l2 : free_monoid X) :
  free_abmonoid_hrel X (l1 * l2) (l2 * l1).
Proof.
  apply wittohexists with l1. split with l2. split; reflexivity.
Defined.

Lemma free_abmonoid_hrel_univ {X : hSet} (P : free_monoid X → free_monoid X → UU)
      (HP : ∏ (x y : free_monoid X), isaprop (P x y))
      (Hind : ∏ x y, P (x * y) (y * x)) (x y : free_monoid X) :
  free_abmonoid_hrel X x y → P x y.
Proof.
  apply (@hinhuniv _ (hProppair (P x y) (HP x y))). intro v.
  induction v as (x',v). induction v as (y',v). induction v as (p1,p2).
  induction p1. induction p2. apply Hind.
Defined.

Definition free_abmonoid' (X : hSet) : monoid :=
  @monoidquot (free_monoid X) (generated_binopeqrel (free_abmonoid_hrel X)).

Lemma iscomm_free_abmonoid (X : hSet) : iscomm (@op (free_abmonoid' X)).
Proof.
  refine (setquotuniv2prop' _ _ _).
  - intros. apply (isasetmonoid (free_abmonoid' X)).
  - intros x1 x2. apply (iscompsetquotpr _ (x1 * x2) (x2 * x1)).
      apply generated_binopeqrel_intro, free_abmonoid_hrel_intro.
Defined.

Definition free_abmonoid (X : hSet) : abmonoid :=
  abmonoid_of_monoid (free_abmonoid' X) (iscomm_free_abmonoid X).

Definition free_abmonoid_pr (X : hSet) : monoidfun (free_monoid X) (free_abmonoid X) :=
  monoidquotpr _.

Definition free_abmonoid_unit {X : hSet} (x : X) : free_abmonoid X :=
   free_abmonoid_pr X (free_monoid_unit x).

Definition free_abmonoid_extend {X : hSet} {Y : abmonoid} (f : X → Y) :
  monoidfun (free_abmonoid X) Y.
Proof.
  use monoidquotuniv.
  - exact (free_monoid_extend f).
  - apply iscomprelfun_generated_binopeqrel. unfold iscomprelfun.
    apply free_abmonoid_hrel_univ.
    + intros. apply (isasetmonoid Y).
    + intros x y. rewrite !monoidfunmul. apply commax.
Defined.

Lemma free_abmonoid_extend_comp {X : hSet} {Y : abmonoid} (g : monoidfun (free_abmonoid X) Y):
  free_abmonoid_extend (g ∘ free_abmonoid_unit) ~ g.
Proof.
  unfold homot. apply setquotunivprop'.
    + intro. apply isasetmonoid.
    + intro x. refine (setquotunivcomm _ _ _ _ _ @ _). simpl.
      apply (free_monoid_extend_comp (monoidfuncomp (free_abmonoid_pr X) g)).
Defined.

Definition isfree_free_abmonoid (X : hSet) (Y : abmonoid) : (X → Y) ≃ monoidfun (free_abmonoid X) Y.
Proof.
  use weq_iso.
  - apply free_abmonoid_extend.
  - intro g. exact (g ∘ free_abmonoid_unit).
  - intro f. apply funextfun. intro x. apply iterop_list_mon_singleton.
  - intro g. apply monoidfun_paths, funextfun, free_abmonoid_extend_comp.
Defined.

Definition free_abmonoidfun {X Y : hSet} (f : X → Y) :
  monoidfun (free_abmonoid X) (free_abmonoid Y) :=
  free_abmonoid_extend (free_abmonoid_unit ∘ f).

(* Free group on a set. We define it as a quotient of the free monoid on X ⨿ X, where (inr x) is to be treated
   as the inverse of x. *)

Definition free_gr_hrel (X : hSet) : hrel (free_monoid (setcoprod X X)) :=
  λ g h, ∃ x, x::coprodcomm X X x::[] = g × [] = h.

Lemma free_gr_hrel_in {X : hSet} (x : X ⨿ X) : free_gr_hrel X (x::coprodcomm X X x::[]) [].
Proof.
  apply wittohexists with x. split; reflexivity.
Defined.

Lemma free_gr_hrel_in_rev {X : hSet} (x : X ⨿ X) : free_gr_hrel X (coprodcomm X X x::x::[]) [].
Proof.
  pose (H := free_gr_hrel_in (coprodcomm X X x)).
  rewrite coprodcomm_coprodcomm in H. exact H.
Defined.

Lemma free_gr_hrel_univ {X : hSet}
      (P : free_monoid (setcoprod X X) → free_monoid (setcoprod X X) → UU)
      (HP : ∏ x y, isaprop (P x y))
      (Hind : ∏ x, P (x::coprodcomm X X x::[]) [])
      (x y : free_monoid (setcoprod X X)) : free_gr_hrel X x y → P x y.
Proof.
  apply (@hinhuniv _ (hProppair (P x y) (HP x y))).
  intro v. induction v as (x',v), v as (p1,p2), p1, p2. apply Hind.
Defined.

(* [fginv x] will be the inverse of [x] in the free group *)
Local Definition fginv {X : hSet} (l : free_monoid (setcoprod X X)) : free_monoid (setcoprod X X) :=
  reverse (map (coprodcomm X X) l).

Definition fginv_binopfun (X : hSet) :
  binopfun (free_monoid (setcoprod X X)) (setwithbinop_rev (free_monoid (setcoprod X X))).
Proof.
  refine (binopfuncomp (free_monoidfun _) (reverse_binopfun _)). exact (coprodcomm X X).
Defined.

Definition fginv_binopfun_homot {X : hSet} (l : free_monoid (setcoprod X X)) :
  fginv_binopfun X l = fginv l :=
  idpath _.

Lemma fginv_fginv {X : hSet} (l : free_monoid (setcoprod X X)) : fginv (fginv l) = l.
Proof.
  unfold fginv. rewrite map_reverse, reverse_reverse, <- map_compose, <- map_idfun.
  apply map_homot. exact coprodcomm_coprodcomm.
Defined.

Lemma generated_free_gr_hrel_in {X : hSet} (l : free_monoid (setcoprod X X)) :
  generated_binopeqrel (free_gr_hrel X) (l * fginv l) [].
Proof.
  intros R H. revert l. apply list_ind.
  - apply eqrelrefl.
  - intros x xs IH.
    change (R ((free_monoid_unit x * xs) * (fginv xs * @free_monoid_unit (setcoprod X X) (coprodcomm X X x)))
              []).
    rewrite assocax, <- (assocax _ _ _ (free_monoid_unit _)).
    refine (eqreltrans (pr1 R) _ _ _ (binopeqrel_resp_left R _ (binopeqrel_resp_right R _ IH)) _).
    apply H, free_gr_hrel_in.
Defined.

Lemma generated_free_gr_hrel_in_rev {X : hSet} (l : free_monoid (setcoprod X X)) :
  generated_binopeqrel (free_gr_hrel X) (fginv l * l) [].
Proof.
  pose (H := generated_free_gr_hrel_in (fginv l)).
  rewrite fginv_fginv in H. exact H.
Defined.

Local Definition free_gr' (X : hSet) : monoid :=
  @monoidquot (free_monoid (setcoprod X X)) (generated_binopeqrel (free_gr_hrel X)).

Definition invstruct_free_gr (X : hSet) : invstruct (@op (free_gr' X)) (pr2 (free_gr' X)).
Proof.
  use mk_invstruct.
  - use setquotfun.
    + exact fginv.
    + refine (iscomprelrelfun_generated_binopeqrel_rev (fginv_binopfun X) _). unfold iscomprelrelfun.
      apply free_gr_hrel_univ.
      * intros. apply pr2.
      * intro x. rewrite fginv_binopfun_homot. apply free_gr_hrel_in_rev.
  - apply mk_isinv.
    + refine (setquotunivprop' _ _ _).
      * intro. apply isasetmonoid.
      * intro l. refine (maponpaths (λ x, x * _) (setquotunivcomm _ _ _ _ _) @ _).
        apply (iscompsetquotpr _ (fginv l * l) []).
        apply generated_free_gr_hrel_in_rev.
    + refine (setquotunivprop' _ _ _).
      * intro. apply isasetmonoid.
      * intro l. refine (maponpaths (λ x, _ * x) (setquotunivcomm _ _ _ _ _) @ _).
        apply (iscompsetquotpr _ (l * fginv l) []).
        apply generated_free_gr_hrel_in.
Defined.

(* The free group is actually a group *)
Definition free_gr (X : hSet) : gr :=
  gr_of_monoid (free_gr' X) (invstruct_free_gr X).

Definition free_gr_pr (X : hSet) : monoidfun (free_monoid (setcoprod X X)) (free_gr X) :=
  monoidquotpr _.

Definition free_gr_unit {X : hSet} (x : X) : free_gr X.
Proof. refine (free_gr_pr X (free_monoid_unit _)). exact (inl x). Defined.

Definition free_gr_extend {X : hSet} {Y : gr} (f : X → Y) :
  monoidfun (free_gr X) Y.
Proof.
  use monoidquotuniv.
  - apply free_monoid_extend. exact (sumofmaps f (grinv Y ∘ f)).
  - apply iscomprelfun_generated_binopeqrel. unfold iscomprelfun.
    apply free_gr_hrel_univ.
    + intros x y. apply (isasetmonoid Y).
    + intro x. induction x as [x|x].
      * apply (grrinvax Y (f x)).
      * apply (grlinvax Y (f x)).
Defined.

Lemma free_gr_extend_comp {X : hSet} {Y : gr} (g : monoidfun (free_gr X) Y):
  free_gr_extend (g ∘ free_gr_unit) ~ g.
Proof.
  unfold homot.
  apply setquotunivprop'.
  - intro. apply (isasetmonoid Y).
  - intro l. refine (setquotunivcomm _ _ _ _ _ @ _).
    refine (_ @ (free_monoid_extend_comp (monoidfuncomp (free_gr_pr X) g)) l).
    apply (maponpaths iterop_list_mon). apply map_homot. intro x.
    induction x as [x|x].
    + reflexivity.
    + simpl. refine (!monoidfuninvtoinv g _ @ _). reflexivity.
Defined.

Definition isfree_free_gr (X : hSet) (Y : gr) : (X → Y) ≃ monoidfun (free_gr X) Y.
Proof.
  use weq_iso.
  - apply free_gr_extend.
  - intro g. exact (g ∘ free_gr_unit).
  - intro f. apply funextfun. intro x. apply iterop_list_mon_singleton.
  - intro g. apply monoidfun_paths, funextfun, free_gr_extend_comp.
Defined.

Definition free_grfun {X Y : hSet} (f : X → Y) : monoidfun (free_gr X) (free_gr Y) :=
  free_gr_extend (free_gr_unit ∘ f).

(* Free abelian group on a set *)

Definition free_abgr_hrel (X : hSet) : hrel (free_gr X) :=
  λ g h, ∃ x y, x * y = g × y * x = h.

Lemma free_abgr_hrel_intro {X : hSet} (l1 l2 : free_gr X) :
  free_abgr_hrel X (l1 * l2) (l2 * l1).
Proof.
  apply wittohexists with l1. split with l2. split; reflexivity.
Defined.

Lemma free_abgr_hrel_univ {X : hSet} (P : free_gr X → free_gr X → UU)
      (HP : ∏ (x y : free_gr X), isaprop (P x y))
      (Hind : ∏ x y, P (x * y) (y * x)) (x y : free_gr X) :
  free_abgr_hrel X x y → P x y.
Proof.
  apply (@hinhuniv _ (hProppair (P x y) (HP x y))). intro v.
  induction v as (x',v). induction v as (y',v). induction v as (p1,p2).
  induction p1. induction p2. apply Hind.
Defined.

Definition free_abgr' (X : hSet) : gr :=
  @grquot (free_gr X) (generated_binopeqrel (free_abgr_hrel X)).

Lemma iscomm_free_abgr (X : hSet) : iscomm (@op (free_abgr' X)).
Proof.
  refine (setquotuniv2prop' _ _ _).
  - intros. apply (isasetmonoid (free_abgr' X)).
  - intros x1 x2. apply (iscompsetquotpr _ (x1 * x2) (x2 * x1)).
      apply generated_binopeqrel_intro, free_abgr_hrel_intro.
Defined.

Definition free_abgr (X : hSet) : abgr :=
  abgr_of_gr (free_abgr' X) (iscomm_free_abgr X).

Definition free_abgr_pr (X : hSet) : monoidfun (free_gr X) (free_abgr X) :=
  monoidquotpr _.

Definition free_abgr_unit {X : hSet} (x : X) : free_abgr X :=
   free_abgr_pr X (free_gr_unit x).

Definition free_abgr_extend {X : hSet} {Y : abgr} (f : X → Y) : monoidfun (free_abgr X) Y.
Proof.
  use monoidquotuniv.
  - exact (free_gr_extend f).
  - apply iscomprelfun_generated_binopeqrel. unfold iscomprelfun.
    apply free_abgr_hrel_univ.
    + intros. apply (isasetmonoid Y).
    + intros x y. rewrite !monoidfunmul. apply (commax Y).
Defined.

Lemma free_abgr_extend_comp {X : hSet} {Y : abgr} (g : monoidfun (free_abgr X) Y):
  free_abgr_extend (g ∘ free_abgr_unit) ~ g.
Proof.
  unfold homot. apply setquotunivprop'.
    + intro. apply isasetmonoid.
    + intro x. refine (setquotunivcomm _ _ _ _ _ @ _). simpl.
      apply (free_gr_extend_comp (monoidfuncomp (free_abgr_pr X) g)).
Defined.

Definition isfree_free_abgr (X : hSet) (Y : abgr) : (X → Y) ≃ monoidfun (free_abgr X) Y.
Proof.
  use weq_iso.
  - apply free_abgr_extend.
  - intro g. exact (g ∘ free_abgr_unit).
  - intro f. apply funextfun. intro x. apply iterop_list_mon_singleton.
  - intro g. apply monoidfun_paths, funextfun, free_abgr_extend_comp.
Defined.

Definition free_abgrfun {X Y : hSet} (f : X → Y) :
  monoidfun (free_abgr X) (free_abgr Y) :=
  free_abgr_extend (free_abgr_unit ∘ f).
