(** Authors Floris van Doorn, December 2017 *)

Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Combinatorics.Lists.

(** ** Contents
- Free monoid on a set
- Monoid presented by a set of generators and relations
- Free abelian monoid on a set
- Abelian monoid presented by a set of generators and relations
- Free group on a set
- Group presented by a set of generators and relations
- Free abelian group on set
- Abelian group presented by a set of generators and relations
*)

Local Open Scope multmonoid_scope.
Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

(* Free monoid on a set *)
Lemma ismonoidop_concatenate (X : UU) : ismonoidop (@concatenate X).
Proof.
  use make_ismonoidop.
  - use assoc_concatenate.
  - use make_isunital.
    + exact [].
    + use make_isunit.
      * use nil_concatenate.
      * use concatenate_nil.
Defined.

Definition free_monoid (X : hSet) : monoid :=
  make_monoid (make_setwithbinop (make_hSet (list X) (isofhlevellist 0 (pr2 X))) _)
             (ismonoidop_concatenate X).

Definition free_monoid_unit {X : hSet} (x : X) : free_monoid X :=
  x::[].

Definition free_monoid_extend {X : hSet} {Y : monoid} (f : X → Y) : monoidfun (free_monoid X) Y.
Proof.
  use monoidfunconstr.
  - intro l. exact (iterop_list_mon (map f l)).
  - use make_ismonoidfun.
    + intros l1 l2. refine (maponpaths _ (map_concatenate _ _ _) @ _).
      apply iterop_list_mon_concatenate.
    + reflexivity.
Defined.

Lemma free_monoid_extend_homot {X : hSet} {Y : monoid} {f f' : X → Y} (h : f ~ f') :
  free_monoid_extend f ~ free_monoid_extend f'.
Proof.
  intro x. apply (maponpaths iterop_list_mon). exact (map_homot h x).
Defined.

Lemma free_monoid_extend_comp {X : hSet} {Y : monoid} (g : monoidfun (free_monoid X) Y):
  free_monoid_extend (g ∘ free_monoid_unit) ~ g.
Proof.
  unfold homot. simpl. apply list_ind.
    + exact (! monoidfununel g).
    + intros x xs IH. rewrite map_cons, iterop_list_mon_step, IH.
      exact (!pr1 (pr2 g) _ _).
Defined.

Definition free_monoid_universal_property (X : hSet) (Y : monoid) : (X → Y) ≃ monoidfun (free_monoid X) Y.
Proof.
  use weq_iso.
  - apply free_monoid_extend.
  - intro g. exact (g ∘ free_monoid_unit).
  - intro f. apply funextfun. intro x. reflexivity.
  - intro g. apply monoidfun_paths. apply funextfun. exact (free_monoid_extend_comp g).
Defined.

(* We don't use free_monoid_extend, so that the underlying function is map *)
Definition free_monoidfun {X Y : hSet} (f : X → Y) : monoidfun (free_monoid X) (free_monoid Y).
Proof.
  use monoidfunconstr.
  - intro l. exact (map f l).
  - use make_ismonoidfun.
    + intros l1 l2. apply map_concatenate.
    + reflexivity.
Defined.

Lemma free_monoidfun_homot_extend {X Y : hSet} (f : X → Y) :
  free_monoidfun f ~ free_monoid_extend (free_monoid_unit ∘ f).
Proof. exact (foldr1_concatenate f). Defined.

Lemma free_monoid_extend_funcomp {X Y : hSet} {Z : monoid} (f : X → Y) (g : Y → Z) :
  free_monoid_extend (g ∘ f) ~ free_monoid_extend g ∘ free_monoidfun f.
Proof.
  unfold homot. simpl. apply list_ind.
    + reflexivity.
    + intros x xs IH. now rewrite !map_cons, !iterop_list_mon_step, IH.
Defined.

(** Functoriality of the [free_monoidfun] *)
Lemma free_monoidfun_comp_homot {X Y Z : hSet} (f : X -> Y) (g : Y -> Z) :
  (free_monoidfun (g ∘ f)) ~ free_monoidfun g ∘ free_monoidfun f.
Proof.
  intro; apply map_compose.
Qed.

Definition reverse_binopfun (X : hSet) :
  binopfun (free_monoid X) (setwithbinop_rev (free_monoid X)).
Proof.
  use make_binopfun.
  - exact reverse.
  - intros x x'. apply reverse_concatenate.
Defined.

(* Monoid presented by a set of generators and relations *)

Definition presented_monoid (X : hSet) (R : hrel (free_monoid X)) : monoid :=
  monoidquot (generated_binopeqrel R).

Definition presented_monoid_pr {X : hSet} (R : hrel (free_monoid X)) :
  monoidfun (free_monoid X) (presented_monoid X R) :=
  monoidquotpr _.

Definition presented_monoid_intro {X : hSet} {R : hrel (free_monoid X)} :
  X → presented_monoid X R :=
  presented_monoid_pr R ∘ free_monoid_unit.

Definition presented_monoid_extend {X : hSet} {R : hrel (free_monoid X)} {Y : monoid} (f : X → Y)
  (H : iscomprelfun R (free_monoid_extend f)) : monoidfun (presented_monoid X R) Y.
Proof.
  use monoidquotuniv.
  - exact (free_monoid_extend f).
  - exact (iscomprelfun_generated_binopeqrel _ H).
Defined.

Lemma iscomprelfun_presented_monoidfun {X : hSet} {R : hrel (free_monoid X)} {Y : monoid}
      (g : monoidfun (presented_monoid X R) Y) :
  iscomprelfun R (free_monoid_extend (g ∘ presented_monoid_intro)).
Proof.
  intros x x' r.
  rewrite !(free_monoid_extend_comp (monoidfuncomp (presented_monoid_pr R) g)).
  apply (maponpaths (pr1 g)). apply iscompsetquotpr. exact (generated_binopeqrel_intro r).
Defined.

Lemma presented_monoid_extend_comp {X : hSet} {R : hrel (free_monoid X)} {Y : monoid}
      (g : monoidfun (presented_monoid X R) Y)
      (H : iscomprelfun R (free_monoid_extend (g ∘ presented_monoid_intro))) :
  presented_monoid_extend (g ∘ presented_monoid_intro) H ~ g.
Proof.
  unfold homot. apply setquotunivprop'.
    + intro. apply isasetmonoid.
    + intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
      exact (free_monoid_extend_comp (monoidfuncomp (presented_monoid_pr R) g) x).
Defined.

Definition presented_monoid_universal_property {X : hSet} (R : hrel (free_monoid X)) (Y : monoid) :
  monoidfun (presented_monoid X R) Y ≃ ∑(f : X → Y), iscomprelfun R (free_monoid_extend f).
Proof.
  use weq_iso.
  - intro g. exact (tpair _ (g ∘ presented_monoid_intro) (iscomprelfun_presented_monoidfun g)).
  - intro f. exact (presented_monoid_extend (pr1 f) (pr2 f)).
  - intro g. apply monoidfun_paths, funextfun, presented_monoid_extend_comp.
  - intro f. use total2_paths_f.
    + apply funextfun. intro x. reflexivity.
    + apply isapropiscomprelfun.
Defined.

Definition presented_monoidfun {X Y : hSet} {R : hrel (free_monoid X)} {S : hrel (free_monoid Y)}
           (f : X → Y) (H : iscomprelrelfun R S (free_monoidfun f)) :
  monoidfun (presented_monoid X R) (presented_monoid Y S).
Proof.
  apply (presented_monoid_extend (presented_monoid_intro ∘ f)).
  intros x x' r.
  rewrite !free_monoid_extend_funcomp. unfold funcomp.
  rewrite !(free_monoid_extend_comp (presented_monoid_pr S)).
  apply iscompsetquotpr. apply generated_binopeqrel_intro. exact (H x x' r).
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
  apply (@hinhuniv _ (make_hProp (P x y) (HP x y))). intro v.
  induction v as (x',v). induction v as (y',v). induction v as (p1,p2).
  induction p1. induction p2. apply Hind.
Defined.

Definition free_abmonoid' (X : hSet) : monoid :=
  presented_monoid X (free_abmonoid_hrel X).

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
  presented_monoid_pr _.

Definition free_abmonoid_unit {X : hSet} (x : X) : free_abmonoid X :=
  presented_monoid_intro x.

Definition free_abmonoid_extend {X : hSet} {Y : abmonoid} (f : X → Y) :
  monoidfun (free_abmonoid X) Y.
Proof.
  apply (presented_monoid_extend f). unfold iscomprelfun. apply free_abmonoid_hrel_univ.
  - intros. apply (isasetmonoid Y).
  - intros x y. rewrite !monoidfunmul. apply commax.
Defined.

Lemma free_abmonoid_extend_homot {X : hSet} {Y : abmonoid} {f f' : X → Y} (h : f ~ f') :
  free_abmonoid_extend f ~ free_abmonoid_extend f'.
Proof.
  unfold homot. apply setquotunivprop'.
  - intro x. apply isasetmonoid.
  - exact (free_monoid_extend_homot h).
Defined.

Lemma free_abmonoid_extend_comp {X : hSet} {Y : abmonoid} (g : monoidfun (free_abmonoid X) Y):
  free_abmonoid_extend (g ∘ free_abmonoid_unit) ~ g.
Proof.
  apply (presented_monoid_extend_comp g).
Defined.

Definition free_abmonoid_universal_property (X : hSet) (Y : abmonoid) : (X → Y) ≃ monoidfun (free_abmonoid X) Y.
Proof.
  use weq_iso.
  - apply free_abmonoid_extend.
  - intro g. exact (g ∘ free_abmonoid_unit).
  - intro f. apply funextfun. intro x. reflexivity.
  - intro g. apply monoidfun_paths, funextfun, free_abmonoid_extend_comp.
Defined.

Definition free_abmonoidfun {X Y : hSet} (f : X → Y) :
  monoidfun (free_abmonoid X) (free_abmonoid Y) :=
  free_abmonoid_extend (free_abmonoid_unit ∘ f).

Lemma free_abmonoidfun_setquotpr {X Y : hSet} (f : X → Y) (x : free_monoid X) :
  free_abmonoidfun f (setquotpr _ x) = setquotpr _ (free_monoidfun f x).
Proof.
  refine (setquotunivcomm _ _ _ _ _ @ _).
  rewrite free_monoid_extend_funcomp.
  apply free_monoid_extend_comp.
Defined.

Lemma free_abmonoid_extend_funcomp {X Y : hSet} {Z : abmonoid} (f : X → Y) (g : Y → Z) :
  free_abmonoid_extend (g ∘ f) ~ free_abmonoid_extend g ∘ free_abmonoidfun f.
Proof.
  unfold homot. apply setquotunivprop'.
  - intro. apply isasetmonoid.
  - intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
    refine (free_monoid_extend_funcomp f g x @ _).
    unfold funcomp. rewrite free_abmonoidfun_setquotpr.
    refine (!setquotunivcomm _ _ _ _ _).
Defined.

(* Abelian monoid presented by a set of generators and relations *)

Definition presented_abmonoid (X : hSet) (R : hrel (free_abmonoid X)) : abmonoid :=
  abmonoidquot (generated_binopeqrel R).

Definition presented_abmonoid_pr {X : hSet} (R : hrel (free_abmonoid X)) :
  monoidfun (free_abmonoid X) (presented_abmonoid X R) :=
  monoidquotpr _.

Definition presented_abmonoid_intro {X : hSet} {R : hrel (free_abmonoid X)} :
  X → presented_abmonoid X R :=
  presented_abmonoid_pr R ∘ free_abmonoid_unit.

Definition presented_abmonoid_extend {X : hSet} {R : hrel (free_abmonoid X)} {Y : abmonoid} (f : X → Y)
  (H : iscomprelfun R (free_abmonoid_extend f)) : monoidfun (presented_abmonoid X R) Y.
Proof.
  use monoidquotuniv.
  - exact (free_abmonoid_extend f).
  - exact (iscomprelfun_generated_binopeqrel _ H).
Defined.

Lemma iscomprelfun_presented_abmonoidfun {X : hSet} {R : hrel (free_abmonoid X)} {Y : abmonoid}
      (g : monoidfun (presented_abmonoid X R) Y) :
  iscomprelfun R (free_abmonoid_extend (g ∘ presented_abmonoid_intro)).
Proof.
  intros x x' r.
  rewrite !(free_abmonoid_extend_comp (monoidfuncomp (presented_abmonoid_pr R) g)).
  apply (maponpaths (pr1 g)). apply iscompsetquotpr. exact (generated_binopeqrel_intro r).
Defined.

Lemma presented_abmonoid_extend_comp {X : hSet} {R : hrel (free_abmonoid X)} {Y : abmonoid}
      (g : monoidfun (presented_abmonoid X R) Y)
      (H : iscomprelfun R (free_abmonoid_extend (g ∘ presented_abmonoid_intro))) :
  presented_abmonoid_extend (g ∘ presented_abmonoid_intro) H ~ g.
Proof.
  unfold homot. apply setquotunivprop'.
    + intro. apply isasetmonoid.
    + intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
      exact (free_abmonoid_extend_comp (monoidfuncomp (presented_abmonoid_pr R) g) x).
Defined.

Definition presented_abmonoid_universal_property {X : hSet} (R : hrel (free_abmonoid X)) (Y : abmonoid) :
  monoidfun (presented_abmonoid X R) Y ≃ ∑(f : X → Y), iscomprelfun R (free_abmonoid_extend f).
Proof.
  use weq_iso.
  - intro g. exact (tpair _ (g ∘ presented_abmonoid_intro) (iscomprelfun_presented_abmonoidfun g)).
  - intro f. exact (presented_abmonoid_extend (pr1 f) (pr2 f)).
  - intro g. apply monoidfun_paths, funextfun, presented_abmonoid_extend_comp.
  - intro f. use total2_paths_f.
    + apply funextfun. intro x. reflexivity.
    + apply isapropiscomprelfun.
Defined.

Definition presented_abmonoidfun {X Y : hSet} {R : hrel (free_abmonoid X)} {S : hrel (free_abmonoid Y)}
           (f : X → Y) (H : iscomprelrelfun R S (free_abmonoidfun f)) :
  monoidfun (presented_abmonoid X R) (presented_abmonoid Y S).
Proof.
  apply (presented_abmonoid_extend (presented_abmonoid_intro ∘ f)).
  intros x x' r.
  rewrite !(free_abmonoid_extend_funcomp _ _ _). unfold funcomp.
  rewrite !(free_abmonoid_extend_comp (presented_abmonoid_pr S)).
  apply iscompsetquotpr. apply generated_binopeqrel_intro. exact (H x x' r).
Defined.

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
  apply (@hinhuniv _ (make_hProp (P x y) (HP x y))).
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
  presented_monoid (setcoprod X X) (free_gr_hrel X).

Definition invstruct_free_gr (X : hSet) : invstruct (@op (free_gr' X)) (pr2 (free_gr' X)).
Proof.
  use make_invstruct.
  - use setquotfun.
    + exact fginv.
    + refine (iscomprelrelfun_generated_binopeqrel_rev (fginv_binopfun X) _). unfold iscomprelrelfun.
      apply free_gr_hrel_univ.
      * intros. apply pr2.
      * intro x. rewrite fginv_binopfun_homot. apply free_gr_hrel_in_rev.
  - apply make_isinv.
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
Proof. apply presented_monoid_intro. exact (inl x). Defined.

Definition free_gr_extend {X : hSet} {Y : gr} (f : X → Y) :
  monoidfun (free_gr X) Y.
Proof.
  use presented_monoid_extend.
  - exact (sumofmaps f (grinv Y ∘ f)).
  - unfold iscomprelfun. apply free_gr_hrel_univ.
    + intros x y. apply (isasetmonoid Y).
    + intro x. induction x as [x|x].
      * apply (grrinvax Y (f x)).
      * apply (grlinvax Y (f x)).
Defined.

Lemma free_gr_extend_homot {X : hSet} {Y : gr} {f f' : X → Y} (h : f ~ f') :
  free_gr_extend f ~ free_gr_extend f'.
Proof.
  unfold homot. apply setquotunivprop'.
  - intro x. apply isasetmonoid.
  - refine (free_monoid_extend_homot _).
    apply sumofmaps_homot.
    + exact h.
    + intro x. exact (maponpaths (grinv Y) (h x)).
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

Definition free_gr_universal_property (X : hSet) (Y : gr) : (X → Y) ≃ monoidfun (free_gr X) Y.
Proof.
  use weq_iso.
  - apply free_gr_extend.
  - intro g. exact (g ∘ free_gr_unit).
  - intro f. apply funextfun. intro x. reflexivity.
  - intro g. apply monoidfun_paths, funextfun, free_gr_extend_comp.
Defined.

Definition free_grfun {X Y : hSet} (f : X → Y) : monoidfun (free_gr X) (free_gr Y) :=
  free_gr_extend (free_gr_unit ∘ f).


Lemma sumofmaps_free_gr_unit {X : hSet} :
  sumofmaps free_gr_unit (grinv (free_gr X) ∘ free_gr_unit) ~
            @presented_monoid_intro (setcoprod X X) (free_gr_hrel X).
Proof.
  intro x. induction x as [x|x]; reflexivity.
Defined.

Lemma free_grfun_setquotpr {X Y : hSet} (f : X → Y) (x : free_monoid (setcoprod X X)) :
  free_grfun f (setquotpr _ x) = setquotpr _ (@free_monoidfun (setcoprod X X) (setcoprod Y Y) (coprodf f f) x).
Proof.
  refine (setquotunivcomm _ _ _ _ _ @ _).
  refine (free_monoid_extend_homot _ x @ _).
  exact (sumofmaps_funcomp f free_gr_unit f (grinv (free_gr Y) ∘ free_gr_unit)).
  rewrite (@free_monoid_extend_funcomp (setcoprod X X) (setcoprod Y Y)).
  refine (free_monoid_extend_homot _ _ @ _).
  exact (sumofmaps_free_gr_unit).
  apply (@free_monoid_extend_comp (setcoprod _ _)).
Defined.

Lemma free_gr_extend_funcomp {X Y : hSet} {Z : gr} (f : X → Y) (g : Y → Z) :
  free_gr_extend (g ∘ f) ~ free_gr_extend g ∘ free_grfun f.
Proof.
  unfold homot. apply setquotunivprop'.
  - intro. apply isasetmonoid.
  - intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
    refine (free_monoid_extend_homot _ x @ _).
    exact (sumofmaps_funcomp f g f (grinv Z ∘ g)).
    refine (@free_monoid_extend_funcomp (setcoprod X X) (setcoprod Y Y) _ _ _ x @ _).
    unfold funcomp. rewrite free_grfun_setquotpr.
    refine (!setquotunivcomm _ _ _ _ _).
Defined.

(* Group presented by a set of generators and relations *)

Definition presented_gr (X : hSet) (R : hrel (free_gr X)) : gr :=
  grquot (generated_binopeqrel R).

Definition presented_gr_pr {X : hSet} (R : hrel (free_gr X)) :
  monoidfun (free_gr X) (presented_gr X R) :=
  monoidquotpr _.

Definition presented_gr_intro {X : hSet} {R : hrel (free_gr X)} :
  X → presented_gr X R :=
  presented_gr_pr R ∘ free_gr_unit.

Definition presented_gr_extend {X : hSet} {R : hrel (free_gr X)} {Y : gr} (f : X → Y)
  (H : iscomprelfun R (free_gr_extend f)) : monoidfun (presented_gr X R) Y.
Proof.
  use monoidquotuniv.
  - exact (free_gr_extend f).
  - exact (iscomprelfun_generated_binopeqrel _ H).
Defined.

Lemma iscomprelfun_presented_grfun {X : hSet} {R : hrel (free_gr X)} {Y : gr}
      (g : monoidfun (presented_gr X R) Y) :
  iscomprelfun R (free_gr_extend (g ∘ presented_gr_intro)).
Proof.
  intros x x' r.
  rewrite !(free_gr_extend_comp (monoidfuncomp (presented_gr_pr R) g)).
  apply (maponpaths (pr1 g)). apply iscompsetquotpr. exact (generated_binopeqrel_intro r).
Defined.

Lemma presented_gr_extend_comp {X : hSet} {R : hrel (free_gr X)} {Y : gr}
      (g : monoidfun (presented_gr X R) Y)
      (H : iscomprelfun R (free_gr_extend (g ∘ presented_gr_intro))) :
  presented_gr_extend (g ∘ presented_gr_intro) H ~ g.
Proof.
  unfold homot. apply setquotunivprop'.
    + intro. apply isasetmonoid.
    + intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
      exact (free_gr_extend_comp (monoidfuncomp (presented_gr_pr R) g) _).
Defined.

Definition presented_gr_universal_property {X : hSet} (R : hrel (free_gr X)) (Y : gr) :
  monoidfun (presented_gr X R) Y ≃ ∑(f : X → Y), iscomprelfun R (free_gr_extend f).
Proof.
  use weq_iso.
  - intro g. exact (tpair _ (g ∘ presented_gr_intro) (iscomprelfun_presented_grfun g)).
  - intro f. exact (presented_gr_extend (pr1 f) (pr2 f)).
  - intro g. apply monoidfun_paths, funextfun, presented_gr_extend_comp.
  - intro f. use total2_paths_f.
    + apply funextfun. intro x. reflexivity.
    + apply isapropiscomprelfun.
Defined.

Definition presented_grfun {X Y : hSet} {R : hrel (free_gr X)} {S : hrel (free_gr Y)}
           (f : X → Y) (H : iscomprelrelfun R S (free_grfun f)) :
  monoidfun (presented_gr X R) (presented_gr Y S).
Proof.
  apply (presented_gr_extend (presented_gr_intro ∘ f)).
  intros x x' r.
  rewrite !(free_gr_extend_funcomp _ _ _). unfold funcomp.
  rewrite !(free_gr_extend_comp (presented_gr_pr S)).
  apply iscompsetquotpr. apply generated_binopeqrel_intro. exact (H x x' r).
Defined.

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
  apply (@hinhuniv _ (make_hProp (P x y) (HP x y))). intro v.
  induction v as (x',v). induction v as (y',v). induction v as (p1,p2).
  induction p1. induction p2. apply Hind.
Defined.

Definition free_abgr' (X : hSet) : gr :=
  presented_gr X (free_abgr_hrel X).

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
   presented_gr_intro x.

Definition free_abgr_extend {X : hSet} {Y : abgr} (f : X → Y) : monoidfun (free_abgr X) Y.
Proof.
  apply (presented_gr_extend f).
  unfold iscomprelfun. apply free_abgr_hrel_univ.
  - intros. apply (isasetmonoid Y).
  - intros x y. rewrite !monoidfunmul. apply (commax Y).
Defined.

Lemma free_abgr_extend_homot {X : hSet} {Y : abgr} {f f' : X → Y} (h : f ~ f') :
  free_abgr_extend f ~ free_abgr_extend f'.
Proof.
  unfold homot. apply setquotunivprop'.
  - intro x. apply isasetmonoid.
  - exact (free_gr_extend_homot h).
Defined.

Lemma free_abgr_extend_comp {X : hSet} {Y : abgr} (g : monoidfun (free_abgr X) Y):
  free_abgr_extend (g ∘ free_abgr_unit) ~ g.
Proof.
  exact (presented_gr_extend_comp g _).
Defined.

Definition free_abgr_universal_property (X : hSet) (Y : abgr) : (X → Y) ≃ monoidfun (free_abgr X) Y.
Proof.
  use weq_iso.
  - apply free_abgr_extend.
  - intro g. exact (g ∘ free_abgr_unit).
  - intro f. apply funextfun. intro x. reflexivity.
  - intro g. apply monoidfun_paths, funextfun, free_abgr_extend_comp.
Defined.

Definition free_abgrfun {X Y : hSet} (f : X → Y) :
  monoidfun (free_abgr X) (free_abgr Y) :=
  free_abgr_extend (free_abgr_unit ∘ f).

Lemma free_abgrfun_setquotpr {X Y : hSet} (f : X → Y) (x : free_gr X) :
  free_abgrfun f (setquotpr _ x) = setquotpr _ (free_grfun f x).
Proof.
  refine (setquotunivcomm _ _ _ _ _ @ _).
  rewrite free_gr_extend_funcomp.
  exact (free_gr_extend_comp _ (free_grfun f x)).
Defined.

Lemma free_abgr_extend_funcomp {X Y : hSet} {Z : abgr} (f : X → Y) (g : Y → Z) :
  free_abgr_extend (g ∘ f) ~ free_abgr_extend g ∘ free_abgrfun f.
Proof.
  unfold homot. apply setquotunivprop'.
  - intro. apply isasetmonoid.
  - intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
    refine (free_gr_extend_funcomp _ _ x @ _).
    unfold funcomp. rewrite free_abgrfun_setquotpr.
    refine (!setquotunivcomm _ _ _ _ _).
Defined.

(* Abelian group presented by a set of generators and relations *)

Definition presented_abgr (X : hSet) (R : hrel (free_abgr X)) : abgr :=
  abgrquot (generated_binopeqrel R).

Definition presented_abgr_pr {X : hSet} (R : hrel (free_abgr X)) :
  monoidfun (free_abgr X) (presented_abgr X R) :=
  monoidquotpr _.

Definition presented_abgr_intro {X : hSet} {R : hrel (free_abgr X)} :
  X → presented_abgr X R :=
  presented_abgr_pr R ∘ free_abgr_unit.

Definition presented_abgr_extend {X : hSet} {R : hrel (free_abgr X)} {Y : abgr} (f : X → Y)
  (H : iscomprelfun R (free_abgr_extend f)) : monoidfun (presented_abgr X R) Y.
Proof.
  use monoidquotuniv.
  - exact (free_abgr_extend f).
  - exact (iscomprelfun_generated_binopeqrel _ H).
Defined.

Lemma iscomprelfun_presented_abgrfun {X : hSet} {R : hrel (free_abgr X)} {Y : abgr}
      (g : monoidfun (presented_abgr X R) Y) :
  iscomprelfun R (free_abgr_extend (g ∘ presented_abgr_intro)).
Proof.
  intros x x' r.
  rewrite !(free_abgr_extend_comp (monoidfuncomp (presented_abgr_pr R) g)).
  apply (maponpaths (pr1 g)). apply iscompsetquotpr. exact (generated_binopeqrel_intro r).
Defined.

Lemma presented_abgr_extend_comp {X : hSet} {R : hrel (free_abgr X)} {Y : abgr}
      (g : monoidfun (presented_abgr X R) Y)
      (H : iscomprelfun R (free_abgr_extend (g ∘ presented_abgr_intro))) :
  presented_abgr_extend (g ∘ presented_abgr_intro) H ~ g.
Proof.
  unfold homot. apply setquotunivprop'.
    + intro. apply isasetmonoid.
    + intro x. refine (setquotunivcomm _ _ _ _ _ @ _).
      exact (free_abgr_extend_comp (monoidfuncomp (presented_abgr_pr R) g) x).
Defined.

Definition presented_abgr_universal_property {X : hSet} (R : hrel (free_abgr X)) (Y : abgr) :
  monoidfun (presented_abgr X R) Y ≃ ∑(f : X → Y), iscomprelfun R (free_abgr_extend f).
Proof.
  use weq_iso.
  - intro g. exact (tpair _ (g ∘ presented_abgr_intro) (iscomprelfun_presented_abgrfun g)).
  - intro f. exact (presented_abgr_extend (pr1 f) (pr2 f)).
  - intro g. apply monoidfun_paths, funextfun, presented_abgr_extend_comp.
  - intro f. use total2_paths_f.
    + apply funextfun. intro x. reflexivity.
    + apply isapropiscomprelfun.
Defined.

Definition presented_abgrfun {X Y : hSet} {R : hrel (free_abgr X)} {S : hrel (free_abgr Y)}
           (f : X → Y) (H : iscomprelrelfun R S (free_abgrfun f)) :
  monoidfun (presented_abgr X R) (presented_abgr Y S).
Proof.
  apply (presented_abgr_extend (presented_abgr_intro ∘ f)).
  intros x x' r.
  rewrite !(free_abgr_extend_funcomp _ _ _). unfold funcomp.
  rewrite !(free_abgr_extend_comp (presented_abgr_pr S)).
  apply iscompsetquotpr. apply generated_binopeqrel_intro. exact (H x x' r).
Defined.
