(** * Lattice *)
(** Catherine Lelay. Nov. 2016 - *)
(**
Definition of a lattice: (Burris, S., & Sankappanavar, H. P. (2006).
A Course in Universal Algebra-With 36 Illustrations. Chapter I)
A lattice is a set with two binary operators min and max such that:
- min and max are associative
- min and max are commutative
- ∏ x y : X, min x (max x y) = x
- ∏ x y : X, max x (min x y) = x

In a lattice, we can define a partial order:
- le := λ (x y : X), min lat x y = x

Lattice with a strict order:
A lattice with a strict order gt is lattice such that:
- ∏ (x y : X), (¬ gt x y) <-> le x y
- ∏ x y z : X, gt x z → gt y z → gt (min x y) z
- ∏ x y z : X, gt z x → gt z y → gt z (max lat x y)

Lattice with a total and decidable order:
- le is total and decidable
- it is a lattice with a strong order *)

(**
Lattice in an abelian monoid:
- compatibility and cancelation of addition for le

Truncated minus is a lattice:
- a function minus such that: ∏ (x y : X), (minus x y) + y = max x y *)

(**
Define new lattices using:
- weq
- abmonoidfrac
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Propositions.
Require Export UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

(** ** Definition *)

Definition islatticeop {X : hSet} (min max : binop X) : UU :=
  ((isassoc min) × (iscomm min))
    × ((isassoc max) × (iscomm max))
    × (isabsorb min max)
    × (isabsorb max min).
Lemma isaprop_islatticeop {X : hSet} (min max : binop X) :
  isaprop (islatticeop min max).
Proof.
  apply isapropdirprod ;
    [ | apply isapropdirprod] ;
    apply isapropdirprod.
  apply isapropisassoc.
  apply isapropiscomm.
  apply isapropisassoc.
  apply isapropiscomm.
  apply isapropisabsorb.
  apply isapropisabsorb.
Qed.

Definition lattice (X : hSet) :=
  ∑ min max : binop X, islatticeop min max.

Definition mklattice {X : hSet} {min max : binop X} : islatticeop min max → lattice X :=
  λ (is : islatticeop min max), min,, max ,, is.

Definition Lmin {X : hSet} (lat : lattice X) : binop X := pr1 lat.
Definition Lmax {X : hSet} (lat : lattice X) : binop X := pr1 (pr2 lat).

(** Bounded lattices *)

Definition bounded_latticeop {X : hSet} (l : lattice X) (bot top : X) :=
  (islunit (Lmax l) bot) × (islunit (Lmin l) top).

Definition bounded_lattice (X : hSet) :=
  ∑ (l : lattice X) (bot top : X), bounded_latticeop l bot top.

Definition mkbounded_lattice {X : hSet} {l : lattice X} {bot top : X} :
  bounded_latticeop l bot top → bounded_lattice X := λ bl, l,, bot,, top,, bl.

Definition bounded_lattice_to_lattice X : bounded_lattice X → lattice X := pr1.
Coercion bounded_lattice_to_lattice : bounded_lattice >-> lattice.

Definition Lbot {X : hSet} (is : bounded_lattice X) : X := pr1 (pr2 is).
Definition Ltop {X : hSet} (is : bounded_lattice X) : X := pr1 (pr2 (pr2 is)).

Section lattice_pty.

Context {X : hSet}
        (lat : lattice X).

Definition isassoc_Lmin : isassoc (Lmin lat) :=
  pr1 (pr1 (pr2 (pr2 lat))).
Definition iscomm_Lmin : iscomm (Lmin lat) :=
  pr2 (pr1 (pr2 (pr2 lat))).
Definition isassoc_Lmax : isassoc (Lmax lat) :=
  pr1 (pr1 (pr2 (pr2 (pr2 lat)))).
Definition iscomm_Lmax : iscomm (Lmax lat) :=
  pr2 (pr1 (pr2 (pr2 (pr2 lat)))).
Definition Lmin_absorb : isabsorb (Lmin lat) (Lmax lat) :=
  pr1 (pr2 (pr2 (pr2 (pr2 lat)))).
Definition Lmax_absorb : isabsorb (Lmax lat) (Lmin lat) :=
  pr2 (pr2 (pr2 (pr2 (pr2 lat)))).

Lemma Lmin_id :
  ∏ x : X, Lmin lat x x = x.
Proof.
  intros x.
  intermediate_path (Lmin lat x (Lmax lat x (Lmin lat x x))).
  - apply maponpaths, pathsinv0, Lmax_absorb.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  ∏ x : X, Lmax lat x x = x.
Proof.
  intros x.
  intermediate_path (Lmax lat x (Lmin lat x (Lmax lat x x))).
  - apply maponpaths, pathsinv0, Lmin_absorb.
  - apply Lmax_absorb.
Qed.

End lattice_pty.

Section bounded_lattice_pty.

Context {X : hSet} (l : bounded_lattice X).

Definition islunit_Lmax_Lbot : islunit (Lmax l) (Lbot l) :=
  pr1 (pr2 (pr2 (pr2 l))).

Definition islunit_Lmin_Ltop : islunit (Lmin l) (Ltop l) :=
  pr2 (pr2 (pr2 (pr2 l))).

Lemma Lmin_Lbot (x : X) : Lmin l (Lbot l) x = Lbot l.
Proof.
now rewrite <- (islunit_Lmax_Lbot x), Lmin_absorb.
Qed.

Lemma Lmax_Ltop (x : X) : Lmax l (Ltop l) x = Ltop l.
Proof.
now rewrite <- (islunit_Lmin_Ltop x), Lmax_absorb.
Qed.

End bounded_lattice_pty.

(** ** Partial order in a lattice *)

(** [Lle] *)

Definition Lle {X : hSet} (lat : lattice X) : hrel X :=
  λ (x y : X), (Lmin lat x y = x)%logic.

Section lattice_le.

Context {X : hSet}
        (lat : lattice X).

Definition isrefl_Lle : isrefl (Lle lat) :=
  Lmin_id lat.
Lemma isantisymm_Lle :
  isantisymm (Lle lat).
Proof.
  intros x y Hxy Hyx.
  apply pathscomp0 with (1 := pathsinv0 Hxy).
  apply pathscomp0 with (2 := Hyx).
  apply iscomm_Lmin.
Qed.
Lemma istrans_Lle :
  istrans (Lle lat).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite !isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma isPartialOrder_Lle :
  isPartialOrder (Lle lat).
Proof.
  split ; [ split | ].
  - exact istrans_Lle.
  - exact isrefl_Lle.
  - exact isantisymm_Lle.
Qed.

Lemma Lmin_le_l :
  ∏ x y : X, Lle lat (Lmin lat x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  ∏ x y : X, Lle lat (Lmin lat x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmin_le_case :
  ∏ x y z : X, Lle lat z x → Lle lat z y → Lle lat z (Lmin lat x y).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite (iscomm_Lmin _ x), <- isassoc_Lmin.
  rewrite (isassoc_Lmin _ _ _ y), Lmin_id.
  rewrite isassoc_Lmin, (iscomm_Lmin _ y).
  rewrite isassoc_Lmin, <- (isassoc_Lmin _ x), Lmin_id.
  apply pathsinv0, isassoc_Lmin.
Qed.

Lemma Lmax_le_l :
  ∏ x y : X, Lle lat x (Lmax lat x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  ∏ x y : X, Lle lat y (Lmax lat x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.
Lemma Lmax_le_case :
  ∏ x y z : X, Lle lat x z → Lle lat y z → Lle lat (Lmax lat x y) z.
Proof.
  intros x y z <- <-.
  set (w := Lmax _ (Lmin _ x z) (Lmin _ y z)).
  assert (c : z = (Lmax lat w z)).
  - unfold w.
    now rewrite isassoc_Lmax, (iscomm_Lmax _ (Lmin _ y z) _),
    (iscomm_Lmin _ y z), Lmax_absorb, iscomm_Lmax, iscomm_Lmin, Lmax_absorb.
  - rewrite c. use (Lmin_absorb lat).
Qed.

Lemma Lmin_le_eq_l :
  ∏ x y : X, Lle lat x y → Lmin lat x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_le_eq_r :
  ∏ x y : X, Lle lat y x → Lmin lat x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_le_eq_l :
  ∏ x y : X, Lle lat y x → Lmax lat x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_le_eq_r :
  ∏ x y : X, Lle lat x y → Lmax lat x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_le_eq_l.
Qed.

End lattice_le.

(** [Lge] *)

Definition Lge {X : hSet} (lat : lattice X) : hrel X :=
  λ x y : X, Lle lat y x.

Section Lge_pty.

Context {X : hSet}
        (lat : lattice X).

Definition isrefl_Lge : isrefl (Lge lat) :=
  isrefl_Lle lat.
Lemma isantisymm_Lge :
  isantisymm (Lge lat).
Proof.
  intros x y Hle Hge.
  apply (isantisymm_Lle lat).
  exact Hge.
  exact Hle.
Qed.
Lemma istrans_Lge :
  istrans (Lge lat).
Proof.
  intros x y z Hxy Hyz.
  apply (istrans_Lle lat) with y.
  exact Hyz.
  exact Hxy.
Qed.
Lemma isPartialOrder_Lge :
  isPartialOrder (Lge lat).
Proof.
  split ; [ split | ].
  - exact istrans_Lge.
  - exact isrefl_Lge.
  - exact isantisymm_Lge.
Qed.

Definition Lmin_ge_l :
  ∏ (x y : X), Lge lat x (Lmin lat x y) :=
  Lmin_le_l lat.
Definition Lmin_ge_r :
  ∏ (x y : X), Lge lat y (Lmin lat x y) :=
  Lmin_le_r lat.
Definition Lmin_ge_case :
  ∏ (x y z : X),
  Lge lat x z → Lge lat y z → Lge lat (Lmin lat x y) z :=
  Lmin_le_case lat.

Definition Lmax_ge_l :
  ∏ (x y : X), Lge lat (Lmax lat x y) x :=
  Lmax_le_l lat.
Definition Lmax_ge_r :
  ∏ (x y : X), Lge lat (Lmax lat x y) y :=
  Lmax_le_r lat.
Definition Lmax_ge_case :
  ∏ x y z : X, Lge lat z x → Lge lat z y → Lge lat z (Lmax lat x y) :=
  Lmax_le_case lat.

Definition Lmin_ge_eq_l :
  ∏ (x y : X), Lge lat y x → Lmin lat x y = x :=
  Lmin_le_eq_l lat.
Definition Lmin_ge_eq_r :
  ∏ (x y : X), Lge lat x y → Lmin lat x y = y :=
  Lmin_le_eq_r lat.

Definition Lmax_ge_eq_l :
  ∏ (x y : X), Lge lat x y → Lmax lat x y = x :=
  Lmax_le_eq_l lat.
Definition Lmax_ge_eq_r :
  ∏ (x y : X), Lge lat y x → Lmax lat x y = y :=
  Lmax_le_eq_r lat.

End Lge_pty.

(** ** Lattice with a strong order *)

Definition islatticewithgtrel {X : hSet} (lat : lattice X) (gt : StrongOrder X) :=
  (∏ x y : X, (¬ (gt x y)) <-> Lle lat x y)
    × (∏ x y z : X, gt x z → gt y z → gt (Lmin lat x y) z)
    × (∏ x y z : X, gt z x → gt z y → gt z (Lmax lat x y)).

Definition latticewithgt (X : hSet) :=
  ∑ (lat : lattice X) (gt : StrongOrder X), islatticewithgtrel lat gt.

Definition lattice_latticewithgt {X : hSet} : latticewithgt X → lattice X :=
  pr1.
Coercion lattice_latticewithgt : latticewithgt >-> lattice.

(** [Lgt] *)

Definition Lgt {X : hSet} (lat : latticewithgt X) : StrongOrder X :=
  pr1 (pr2 lat).

Section latticewithgt_pty.

Context {X : hSet}
        (lat : latticewithgt X).

Definition notLgt_Lle :
  ∏ x y : X, (¬ Lgt lat x y) → Lle lat x y :=
  λ x y : X, pr1 (pr1 (pr2 (pr2 lat)) x y).
Definition Lle_notLgt :
  ∏ x y : X, Lle lat x y → ¬ Lgt lat x y :=
  λ x y : X, pr2 (pr1 (pr2 (pr2 lat)) x y).

Definition isirrefl_Lgt : isirrefl (Lgt lat) :=
  isirrefl_StrongOrder (Lgt lat).
Definition istrans_Lgt : istrans (Lgt lat) :=
  istrans_StrongOrder (Lgt lat).
Definition iscotrans_Lgt : iscotrans (Lgt lat) :=
  iscotrans_StrongOrder (Lgt lat).
Definition isasymm_Lgt : isasymm (Lgt lat) :=
  isasymm_StrongOrder (Lgt lat).

Lemma Lgt_Lge :
  ∏ x y : X, Lgt lat x y → Lge lat x y.
Proof.
  intros x y H.
  apply notLgt_Lle.
  intro H0.
  eapply isasymm_Lgt.
  exact H.
  exact H0.
Qed.

Lemma istrans_Lgt_Lge :
  ∏ x y z : X, Lgt lat x y → Lge lat y z → Lgt lat x z.
Proof.
  intros x y z Hgt Hge.
  generalize (iscotrans_Lgt _ z _ Hgt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - exact H.
  - apply fromempty.
    refine (Lle_notLgt _ _ _ _).
    exact Hge.
    exact H.
Qed.
Lemma istrans_Lge_Lgt :
  ∏ x y z : X, Lge lat x y → Lgt lat y z → Lgt lat x z.
Proof.
  intros x y z Hge Hgt.
  generalize (iscotrans_Lgt _ x _ Hgt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - apply fromempty.
    refine (Lle_notLgt _ _ _ _).
    exact Hge.
    exact H.
  - exact H.
Qed.

Definition Lmin_Lgt :
  ∏ x y z : X, Lgt lat x z → Lgt lat y z → Lgt lat (Lmin lat x y) z :=
  pr1 (pr2 (pr2 (pr2 lat))).

Definition Lmax_Lgt :
  ∏ x y z : X, Lgt lat z x → Lgt lat z y → Lgt lat z (Lmax lat x y) :=
  pr2 (pr2 (pr2 (pr2 lat))).

End latticewithgt_pty.

(** ** Lattice with a total order *)

Definition latticedec (X : hSet) :=
  ∑ lat : lattice X, istotal (Lle lat) × (isdecrel (Lle lat)).
Definition lattice_latticedec {X : hSet} (lat : latticedec X) : lattice X :=
  pr1 lat.
Coercion lattice_latticedec : latticedec >-> lattice.
Definition istotal_latticedec {X : hSet} (lat : latticedec X) : istotal (Lle lat) :=
  pr1 (pr2 lat).
Definition isdecrel_latticedec {X : hSet} (lat : latticedec X) : isdecrel (Lle lat) :=
  pr2 (pr2 lat).

Section latticedec_pty.

Context {X : hSet}
        (lat : latticedec X).

Lemma Lmin_case_strong :
  ∏ (P : X → UU) (x y : X),
  (Lle lat x y → P x) → (Lle lat y x → P y) → P (Lmin lat x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_latticedec lat x y).
  apply sumofmaps ; intros H.
  - rewrite Lmin_le_eq_l.
    apply Hx, H.
    exact H.
  - enough (H0 : Lle lat y x).
    + rewrite Lmin_le_eq_r.
      apply Hy, H0.
      exact H0.
    + generalize (istotal_latticedec lat x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmin_case :
  ∏ (P : X → UU) (x y : X),
  P x → P y → P (Lmin lat x y).
Proof.
  intros P x y Hx Hy.
  apply Lmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma Lmax_case_strong :
  ∏ (P : X → UU) (x y : X),
  (Lle lat y x → P x) → (Lle lat x y → P y) → P (Lmax lat x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_latticedec lat x y).
  apply sumofmaps ; intros H.
  - rewrite Lmax_le_eq_r.
    apply Hy, H.
    exact H.
  - enough (H0 : Lle lat y x).
    + rewrite Lmax_le_eq_l.
      apply Hx, H0.
      exact H0.
    + generalize (istotal_latticedec lat x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmax_case :
  ∏ (P : X → UU) (x y : X),
  P x → P y → P (Lmax lat x y).
Proof.
  intros P x y Hx Hy.
  apply Lmax_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

End latticedec_pty.

(** It is a lattice with a strong order *)

Section latticedec_gt.

Context {X : hSet}
        (lat : latticedec X).

Definition latticedec_gt_rel : hrel X :=
  λ x y, hneg (Lle lat x y).

Lemma latticedec_gt_ge :
  ∏ x y : X, latticedec_gt_rel x y → Lge lat x y.
Proof.
  intros x y Hxy.
  generalize (istotal_latticedec lat x y).
  apply hinhuniv, sumofmaps ; intros H.
  - apply fromempty.
    exact (Hxy H).
  - exact H.
Qed.

Lemma istrans_latticedec_gt_rel :
  istrans latticedec_gt_rel.
Proof.
  intros x y z Hxy Hyz Hxz.
  simple refine (Hxy _).
  apply istrans_Lle with z.
  apply Hxz.
  apply latticedec_gt_ge.
  exact Hyz.
Qed.
Lemma iscotrans_latticedec_gt_rel :
  iscotrans latticedec_gt_rel.
Proof.
  intros x y z Hxz.
  induction (isdecrel_latticedec lat x y) as [Hxy | Hyx].
  - apply hinhpr, ii2.
    intros Hyz.
    simple refine (Hxz _).
    apply istrans_Lle with y.
    exact Hxy.
    exact Hyz.
  - apply hinhpr, ii1.
    exact Hyx.
Qed.

Definition latticedec_gt_so : StrongOrder X.
Proof.
  exists latticedec_gt_rel.
  repeat split.
  - apply istrans_latticedec_gt_rel.
  - apply iscotrans_latticedec_gt_rel.
  - intros x Hx.
    simple refine (Hx _).
    apply isrefl_Lle.
Defined.

Lemma latticedec_notgtle :
  ∏ (x y : X), ¬ latticedec_gt_so x y → Lle lat x y.
Proof.
  intros x y H.
  induction (isdecrel_latticedec lat x y) as [H0 | H0].
  + exact H0.
  + apply fromempty, H.
    exact H0.
Qed.

Lemma latticedec_lenotgt :
  ∏ (x y : X), Lle lat x y → ¬ latticedec_gt_so x y.
Proof.
  intros x y H H0.
  simple refine (H0 _).
  exact H.
Qed.

Lemma latticedec_gtmin :
  ∏ (x y z : X),
  latticedec_gt_so x z
  → latticedec_gt_so y z → latticedec_gt_so (Lmin lat x y) z.
Proof.
  intros x y z Hxz Hyz.
  apply (Lmin_case lat (λ t : X, latticedec_gt_so t z)).
  - exact Hxz.
  - exact Hyz.
Qed.

Lemma latticedec_gtmax :
  ∏ (x y z : X),
  latticedec_gt_so z x
  → latticedec_gt_so z y → latticedec_gt_so z (Lmax lat x y).
Proof.
  intros x y z Hxz Hyz.
  apply (Lmax_case lat (latticedec_gt_so z)).
  - exact Hxz.
  - exact Hyz.
Qed.

Definition latticedec_gt : latticewithgt X.
Proof.
  exists (lattice_latticedec lat).
  exists latticedec_gt_so.
  split ; split.
  - apply latticedec_notgtle.
  - apply latticedec_lenotgt.
  - apply latticedec_gtmin.
  - apply latticedec_gtmax.
Defined.

End latticedec_gt.

(** ** Lattice in an abmonoid *)

Local Open Scope addmonoid.
Import UniMath.Algebra.Monoids.AddNotation.

Section lattice_abmonoid.

Context {X : abmonoid}
        (lat : lattice X)
        (is0 : isinvbinophrel (λ x y : X, (x = y)%logic))
        (is2 : isrdistr (Lmin lat) op).

Lemma op_le_r :
  ∏ k x y : X, Lle lat x y → Lle lat (x + k) (y + k).
Proof.
  intros k x y H.
  unfold Lle ; simpl.
  now rewrite <- is2, H.
Qed.
Lemma op_le_r' :
  ∏ k x y : X, Lle lat (x + k) (y + k) → Lle lat x y.
Proof.
  intros k x y H.
  apply (pr2 is0 _ _ k).
  now rewrite is2, H.
Qed.

End lattice_abmonoid.

(** ** Truncated minus *)

Definition istruncminus {X : abmonoid} (lat : lattice X) (minus : binop X) :=
  ∏ x y : X, minus x y + y = Lmax lat x y.
Lemma isaprop_istruncminus {X : abmonoid} (lat : lattice X) (minus : binop X) :
  isaprop (istruncminus lat minus).
Proof.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply setproperty.
Qed.

Definition extruncminus {X : abmonoid} (lat : lattice X) :=
  ∑ minus : binop X, istruncminus lat minus.
Lemma isaprop_extruncminus {X : abmonoid} (lat : lattice X)
      (Hop : isinvbinophrel (λ x y : X, (x = y)%logic)) :
  isaprop (extruncminus lat).
Proof.
  intros minus1 minus2 ; simpl.
  apply iscontraprop1.
  - apply isaset_total2.
    apply impred_isaset ; intros _.
    apply impred_isaset ; intros _.
    apply setproperty.
    intros minus.
    apply isasetaprop.
    apply isaprop_istruncminus.
  - apply subtypePath.
    + intros f. apply isaprop_istruncminus.
    + apply weqfunextsec ; intros x.
      apply weqfunextsec ; intros y.
      apply (pr2 Hop _ _ y).
      rewrite (pr2 minus1).
      apply pathsinv0, (pr2 minus2).
Qed.

Definition truncminus {X : abmonoid} {lat : lattice X} (ex : extruncminus lat) : binop X :=
  pr1 ex.

Lemma istruncminus_ex {X : abmonoid} {lat : lattice X} (ex : extruncminus lat) :
  ∏ x y : X, truncminus ex x y + y = Lmax lat x y.
Proof.
  apply (pr2 ex).
Qed.

Section truncminus_pty.

Context {X : abmonoid}
        {lat : lattice X}
        (ex : extruncminus lat)
        (is1 : isinvbinophrel (λ x y : X, (x = y)%logic))
        (is2 : isrdistr (Lmax lat) op)
        (is3 : isrdistr (Lmin lat) op)
        (is4 : isrdistr (Lmin lat) (Lmax lat))
        (is5 : isrdistr (Lmax lat) (Lmin lat)).

Lemma truncminus_0_r :
  ∏ x : X, truncminus ex x 0 = Lmax lat x 0.
Proof.
  intros x.
  rewrite <- (runax _ (truncminus _ _ _)).
  apply (istruncminus_ex).
Qed.

Lemma truncminus_eq_0 :
  ∏ x y : X, Lle lat x y → truncminus ex x y = 0.
Proof.
  intros x y H.
  apply (pr2 is1 _ _ y).
  simpl.
  refine (pathscomp0 _ _).
  apply istruncminus_ex.
  refine (pathscomp0 _ _).
  apply Lmax_le_eq_r, H.
  apply pathsinv0, (lunax X).
Qed.

Lemma truncminus_0_l_ge0 :
  ∏ x : X, Lle lat 0 x → truncminus ex 0 x = 0.
Proof.
  intros x Hx.
  apply truncminus_eq_0, Hx.
Qed.
Lemma truncminus_0_l_le0 :
  ∏ x : X, Lle lat x 0 → truncminus ex 0 x + x = 0.
Proof.
  intros x Hx.
  rewrite istruncminus_ex.
  apply Lmax_le_eq_l, Hx.
Qed.

Lemma truncminus_ge_0 :
  ∏ x y : X, Lle lat 0 (truncminus ex x y).
Proof.
  intros x y.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex, lunax.
  apply Lmax_ge_r.
Qed.

Lemma truncminus_le :
  ∏ x y : X,
          Lle lat 0 x → Lle lat 0 y
          → Lle lat (truncminus ex x y) x.
Proof.
  intros x y Hx Hy.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex.
  apply Lmax_le_case.
  - apply istrans_Lle with (0 + x).
    + rewrite (lunax _ x).
      apply isrefl_Lle.
    + rewrite (commax _ x).
      now apply op_le_r.
  - apply istrans_Lle with (0 + y).
    + rewrite (lunax _ y).
      apply isrefl_Lle.
    + now apply op_le_r.
Qed.

Lemma truncminus_truncminus :
  ∏ x y, Lle lat 0 x → Lle lat x y → truncminus ex y (truncminus ex y x) = x.
Proof.
  intros x y Hx Hxy.
  apply (pr2 is1 _ _ (truncminus ex y x)).
  simpl.
  rewrite (commax _ x), istruncminus_ex.
  refine (pathscomp0 _ _).
  apply istruncminus_ex.
  rewrite !Lmax_le_eq_l.
  - reflexivity.
  - exact Hxy.
  - apply truncminus_le.
    apply istrans_Lle with x.
    exact Hx.
    exact Hxy.
    exact Hx.
Qed.

Lemma truncminus_le_r :
  ∏ k x y : X, Lle lat x y → Lle lat (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y <-.
  apply (pr2 is1 _ _ k).
  simpl.
  rewrite is3, 2!istruncminus_ex.
  rewrite is4, isassoc_Lmin, Lmin_id.
  rewrite <- is4.
  apply pathsinv0, istruncminus_ex.
Qed.
Lemma truncminus_le_l :
  ∏ k x y : X, Lle lat y x → Lle lat (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (pr2 is1 _ _ y).
  change ((Lmin lat (truncminus ex k x) (truncminus ex k y) * y)%multmonoid =
     (truncminus ex k x * y)%multmonoid).
  rewrite is3, istruncminus_ex.
  apply (pr2 is1 _ _ x).
  change ((Lmin lat (truncminus ex k x * y) (Lmax lat k y) * x)%multmonoid =
     (truncminus ex k x * y * x)%multmonoid).
  rewrite is3, assocax, (commax _ y), <- assocax, istruncminus_ex.
  rewrite !is2, (commax _ y), <- is4, !(commax _ k), <- is3, H.
  reflexivity.
Qed.

Lemma truncminus_Lmax_l :
  ∏ (k x y : X),
  truncminus ex (Lmax lat x y) k = Lmax lat (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (pr2 is1 _ _ k).
  change ((truncminus ex (Lmax lat x y) k * k)%multmonoid =
     (Lmax lat (truncminus ex x k) (truncminus ex y k) * k)%multmonoid).
  rewrite is2, !istruncminus_ex.
  rewrite !isassoc_Lmax, (iscomm_Lmax _ k), isassoc_Lmax, Lmax_id.
  reflexivity.
Qed.
Lemma truncminus_Lmax_r :
  ∏ (k x y : X),
  Lle lat (Lmin lat (y + y) (x + x)) (x + y) →
  truncminus ex k (Lmax lat x y) = Lmin lat (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (pr2 is1 _ _ (Lmax lat x y)).
  change ((truncminus ex k (Lmax lat x y) * Lmax lat x y)%multmonoid =
     (Lmin lat (truncminus ex k x) (truncminus ex k y) * Lmax lat x y)%multmonoid).
  rewrite is3, istruncminus_ex.
  rewrite !(commax _ _ (Lmax _ _ _)), !is2.
  rewrite !(commax _ _ (truncminus _ _ _)), !istruncminus_ex.
  rewrite (iscomm_Lmax _ (_*_)%multmonoid (Lmax _ _ _)).
  rewrite !isassoc_Lmax, !(iscomm_Lmax _ k).
  rewrite <- is4.

  apply (pr2 is1 _ _ x).
  change ((Lmax lat (Lmax lat x y) k * x)%multmonoid =
     (Lmax lat
        (Lmin lat (Lmax lat x (truncminus ex k x * y))
           (Lmax lat y (truncminus ex k y * x))) k * x)%multmonoid).
  rewrite !is2, is3, !is2.
  rewrite assocax, (commax _ y x), <- assocax.
  rewrite istruncminus_ex, is2.

  apply (pr2 is1 _ _ y).
  change ((Lmax lat (Lmax lat (x * x) (x * y)) (k * x) * y)%multmonoid =
     (Lmax lat
        (Lmin lat (Lmax lat (x * x) (Lmax lat (k * y) (x * y)))
           (Lmax lat (x * y) (truncminus ex k y * x * x)))
        (k * x) * y)%multmonoid).
  rewrite !is2, is3, !is2.
  rewrite !assocax, (commax _ (truncminus _ _ _)), !assocax, (commax _ _ (truncminus _ _ _)).
  rewrite istruncminus_ex.
  rewrite (commax _ _ (Lmax _ _ _)), is2.
  rewrite (commax _ _ (Lmax _ _ _)), is2.

  rewrite 4!(commax _ _ x).
  rewrite <- (isassoc_Lmax _ _ _ (x * (y * y))%multmonoid).
  rewrite (iscomm_Lmax _ (x * (y * y))%multmonoid (Lmax _ _ _)).

  rewrite <- is4.
  rewrite (iscomm_Lmax _ (x * (x * y))%multmonoid (k * (y * y))%multmonoid), <- is4.
  rewrite !(commax _ k), <- !assocax.
  rewrite <- is3.
  rewrite !(iscomm_Lmax _ _ (x * y * k)%multmonoid), <- !isassoc_Lmax.
  rewrite (Lmax_le_eq_l _ (x * y * k)%multmonoid
                     (Lmin lat (y * y) (x * x) * k)%multmonoid).
  reflexivity.
  apply op_le_r.
  exact is3.
  exact H.
Qed.

Lemma truncminus_Lmin_l :
  ∏ k x y : X, truncminus ex (Lmin lat x y) k = Lmin lat (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (pr2 is1 _ _ k).
  simpl.
  rewrite is3, 2!istruncminus_ex.
  apply (pathscomp0 (istruncminus_ex _ _ _)).
  apply is4.
Qed.

End truncminus_pty.

Lemma abgr_truncminus {X : abgr} (lat : lattice X) :
  isrdistr (Lmax lat) op →
  istruncminus (X := abgrtoabmonoid X) lat (λ x y : X, Lmax lat 0 (x + grinv X y)).
Proof.
  intros H x y.
  rewrite H, assocax, grlinvax, lunax, runax.
  apply iscomm_Lmax.
Qed.

Section truncminus_gt.

Context {X : abmonoid}
        (lat : latticewithgt X)
        (ex : extruncminus lat)
        (is0 : ∏ x y z : X, Lgt lat y z → Lgt lat (y + x) (z + x))
        (is1 : ∏ x y z : X, Lgt lat (y + x) (z + x) → Lgt lat y z).

Lemma truncminus_pos :
  ∏ x y : X, Lgt lat x y → Lgt lat (truncminus ex x y) 0.
Proof.
  intros x y.
  intros H.
  apply (is1 y).
  rewrite lunax, istruncminus_ex.
  rewrite Lmax_le_eq_l.
  exact H.
  apply Lgt_Lge, H.
Qed.

Lemma truncminus_pos' :
  ∏ x y : X, Lgt lat (truncminus ex x y) 0 → Lgt lat x y.
Proof.
  intros x y Hgt.
  apply (is0 y) in Hgt.
  rewrite istruncminus_ex, lunax in Hgt.
  rewrite <- (Lmax_le_eq_l lat x y).
  exact Hgt.
  apply notLgt_Lle.
  intros H ; revert Hgt.
  apply Lle_notLgt.
  rewrite Lmax_le_eq_r.
  apply isrefl_Lle.
  apply Lgt_Lge.
  exact H.
Qed.

End truncminus_gt.

Close Scope addmonoid.

(** ** lattice and [weq] *)

(** *** Definition *)

Lemma islatticeop_weq {X Y : hSet} (H : weq Y X) {min max : binop X} (lat : islatticeop min max) :
  islatticeop (binop_weq_bck H min) (binop_weq_bck H max).
Proof.
  intros.
  split ; [ | split] ; split.
  - apply (isassoc_weq_bck H), (isassoc_Lmin (_,,_,,lat)).
  - apply (iscomm_weq_bck H), (iscomm_Lmin (_,,_,,lat)).
  - apply (isassoc_weq_bck H), (isassoc_Lmax (_,,_,,lat)).
  - apply (iscomm_weq_bck H), (iscomm_Lmax (_,,_,,lat)).
  - apply (isabsorb_weq_bck H), (Lmin_absorb (_,,_,,lat)).
  - apply (isabsorb_weq_bck H), (Lmax_absorb (_,,_,,lat)).
Qed.

Definition lattice_weq {X Y : hSet} (H : weq Y X) (lat : lattice X) : lattice Y.
Proof.
  exists (binop_weq_bck H (Lmin lat)), (binop_weq_bck H (Lmax lat)).
  apply islatticeop_weq.
  apply (pr2 (pr2 lat)).
Defined.

(** *** Value of [Lle] *)

Lemma Lle_correct_weq {X Y : hSet} (H : weq Y X) (lat : lattice X) :
  fun_hrel_comp H (Lle lat) = Lle (lattice_weq H lat).
Proof.
  apply funextfun ; intros x.
  apply funextfun ; intros y.
  apply hPropUnivalence ; intros Hle.
  - apply pathsinv0, pathsweq1, pathsinv0.
    apply Hle.
  - apply pathsinv0, pathsweq1', pathsinv0.
    apply Hle.
Qed.

(** *** Lattice with strong order *)

Lemma islatticewithgtrel_weq {X Y : hSet} (H : weq Y X) {gt : StrongOrder X} (lat : lattice X) :
  islatticewithgtrel lat gt →
  islatticewithgtrel (lattice_weq H lat) (StrongOrder_bck H gt).
Proof.
  intros Hgt.
  split ; split.
  - intros Hngt.
    unfold Lle ; simpl.
    unfold binop_weq_bck.
    rewrite (pr1 (pr1 Hgt _ _)).
    apply homotinvweqweq.
    apply Hngt.
  - intros Hle.
    apply (pr2 (pr1 Hgt _ _)).
    unfold Lle ; simpl.
    apply pathsinv0, pathsweq1', pathsinv0.
    apply Hle.
  - simpl ; intros x y z Hx Hy.
    unfold binop_weq_bck, fun_hrel_comp.
    rewrite homotweqinvweq.
    apply (pr1 (pr2 Hgt)).
    exact Hx.
    exact Hy.
  - unfold Lmax ; simpl ; intros x y z Hx Hy.
    unfold binop_weq_bck, fun_hrel_comp.
    rewrite homotweqinvweq.
    apply (pr2 (pr2 Hgt)).
    exact Hx.
    exact Hy.
Qed.
Definition latticewithgt_weq {X Y : hSet} (H : weq Y X) (lat : latticewithgt X) :
  latticewithgt Y.
Proof.
  exists (lattice_weq H lat), (StrongOrder_bck H (Lgt lat)).
  apply islatticewithgtrel_weq.
  apply (pr2 (pr2 lat)).
Defined.

(** *** Lattice with a decidable order *)

Lemma istotal_Lle_weq {X Y : hSet} (H : weq Y X)
      (lat : lattice X) (is' : istotal (Lle lat)) :
  istotal (Lle (lattice_weq H lat)).
Proof.
  intros x y.
  generalize (is' (H x) (H y)).
  apply hinhfun, sumofmaps ; intros Hmin.
  - apply ii1, (pathscomp0 (maponpaths (invmap H) Hmin)), homotinvweqweq.
  - apply ii2, (pathscomp0 (maponpaths (invmap H) Hmin)), homotinvweqweq.
Qed.
Lemma isdecrel_Lle_weq {X Y : hSet} (H : weq Y X)
      (lat : lattice X) (is' : isdecrel (Lle lat)) :
  isdecrel (Lle (lattice_weq H lat)).
Proof.
  intros x y.
  generalize (is' (H x) (H y)).
  apply sumofmaps ; intros Hmin.
  - apply ii1, (pathscomp0 (maponpaths (invmap H) Hmin)), homotinvweqweq.
  - apply ii2.
    intros Hinv ; apply Hmin.
    apply pathsinv0, pathsweq1', pathsinv0, Hinv.
Qed.

Definition latticedec_weq {X Y : hSet} (H : weq Y X) :
  latticedec X → latticedec Y.
Proof.
  intros lat.
  exists (lattice_weq H (lattice_latticedec lat)).
  split.
  - apply istotal_Lle_weq.
    apply istotal_latticedec.
  - apply isdecrel_Lle_weq.
    apply isdecrel_latticedec.
Defined.

(** ** lattice in [abmonoid] *)

Open Scope multmonoid.

Lemma abmonoidfrac_setquotpr_equiv {X : abmonoid} {Y : @submonoid X} :
  ∏ (k : Y) (x : X) (y : Y),
  setquotpr (binopeqrelabmonoidfrac X Y) (x,,y) = setquotpr (binopeqrelabmonoidfrac X Y) (x * pr1 k,, @op Y y k).
Proof.
  intros k x y.
  apply iscompsetquotpr, hinhpr.
  exists y ; simpl.
  rewrite !(assocax X) ;
    apply maponpaths.
  rewrite commax, !assocax.
  reflexivity.
Qed.

Definition ispartrdistr {X : abmonoid} (Y : @submonoid X) (opp1 opp2 : binop X) :=
  ∏ (x y : X) (k : Y),
  opp2 (opp1 x y) (pr1 k) = opp1 (opp2 x (pr1 k)) (opp2 y (pr1 k)).

Section abmonoidfrac_lattice.

Context (X : abmonoid)
        (Y : @submonoid X)
        {min max : binop X}
        (Hmin_assoc : isassoc min)
        (Hmin_comm : iscomm min)
        (Hmax_assoc : isassoc max)
        (Hmax_comm : iscomm max)
        (Hmin_max : isabsorb min max)
        (Hmax_min : isabsorb max min)
        (Hmin : ispartrdistr Y min op)
        (Hmax : ispartrdistr Y max op).

(** generic lemmas *)

Local Definition abmonoidfrac_lattice_fun (f : binop X) : binop (X × Y) :=
  λ x y,
  (f (pr1 x * pr1 (pr2 y))%multmonoid (pr1 y * pr1 (pr2 x))%multmonoid ,, @op Y (pr2 x) (pr2 y)).

Local Lemma abmonoidfrac_lattice_def :
  ∏ (f : X → X → X),
  ispartrdistr Y f op →
  iscomprelrelfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y)
                   (abmonoidfrac_lattice_fun f).
Proof.
  intros f Hf.
  intros x y x' y'.
  apply hinhfun2.
  intros c c'.
  unfold abmonoidfrac_lattice_fun.
  change (∑ a0 : Y,
  f (pr1 x * pr1 (pr2 x')) (pr1 x' * pr1 (pr2 x)) *
  pr1 (pr2 y * pr2 y') * pr1 a0 =
  f (pr1 y * pr1 (pr2 y')) (pr1 y' * pr1 (pr2 y)) *
  pr1 (pr2 x * pr2 x') * pr1 a0).
  exists (@op Y (pr1 c) (pr1 c')).
  - do 4 rewrite Hf.
    apply map_on_two_paths.
    + change ((pr1 x * pr1 (pr2 x') * (pr1 (pr2 y) * pr1 (pr2 y')) * (pr1 (pr1 c) * pr1 (pr1 c')))%multmonoid =
  (pr1 y * pr1 (pr2 y') * (pr1 (pr2 x) * pr1 (pr2 x')) * (pr1 (pr1 c) * pr1 (pr1 c')))%multmonoid).
      rewrite (assocax X (pr1 x)), (assocax X (pr1 y)).
      rewrite (commax X (pr1 (pr2 x'))), (commax X (pr1 (pr2 y'))).
      do 2 rewrite <- (assocax X (pr1 x)), <- (assocax X (pr1 y)).
      do 2 rewrite (assocax X (pr1 x * pr1 (pr2 y))%multmonoid), (assocax X (pr1 y * pr1 (pr2 x))%multmonoid).
      do 2 rewrite (commax X _ (pr1 (pr1 c) * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c) * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c))%multmonoid).
      rewrite (commax X (pr1 (pr2 y'))).
      apply (maponpaths (λ x, (x * _ * _)%multmonoid)).
      apply (pr2 c).
    + rewrite (commax _ (pr2 y)), (commax _ (pr2 x)), (iscommcarrier Y (pr1 c)).
      change ((pr1 x' * pr1 (pr2 x) * (pr1 (pr2 y') * pr1 (pr2 y)) * (pr1 (pr1 c') * pr1 (pr1 c)))%multmonoid =
  (pr1 y' * pr1 (pr2 y) * (pr1 (pr2 x') * pr1 (pr2 x)) * (pr1 (pr1 c') * pr1 (pr1 c)))%multmonoid).
      rewrite (assocax X (pr1 x')), (assocax X (pr1 y')).
      rewrite (commax X (pr1 (pr2 x))), (commax X (pr1 (pr2 y))).
      do 2 rewrite <- (assocax X (pr1 x')), <- (assocax X (pr1 y')).
      do 2 rewrite (assocax X (pr1 x' * pr1 (pr2 y'))%multmonoid), (assocax X (pr1 y' * pr1 (pr2 x'))%multmonoid).
      do 2 rewrite (commax X _ (pr1 (pr1 c') * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c') * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c'))%multmonoid).
      rewrite (commax X (pr1 (pr2 y))).
      apply (maponpaths (λ x, (x * _ * _)%multmonoid)).
      apply (pr2 c').
Qed.

Local Lemma iscomm_abmonoidfrac_def :
  ∏ (f : X → X → X) Hf,
  iscomm f →
  iscomm (X := abmonoidfrac X Y)
         (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                      (abmonoidfrac_lattice_def f Hf)).
Proof.
  intros f Hf Hcomm.
  simple refine (setquotuniv2prop _ (λ x y, (_ x y = _ y x) ,, _) _).
  - apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  - intros x y.
    simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    unfold abmonoidfrac_lattice_fun.
    rewrite Hcomm, (commax X (pr1 x)), (commax _ (pr2 x)).
    reflexivity.
Qed.
Local Lemma isassoc_abmonoidfrac_def :
  ∏ (f : X → X → X) Hf,
  isassoc f →
  isassoc (X := abmonoidfrac X Y)
         (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                      (abmonoidfrac_lattice_def f Hf)).
Proof.
  intros f Hf Hassoc.
  simple refine (setquotuniv3prop _ (λ x y z, (_ (_ x y) z = _ x (_ y z)) ,, _) _).
  - apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  - intros x y z ; simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    apply (iscompsetquotpr (eqrelabmonoidfrac X Y)), hinhpr.
    exists (pr2 x).
    apply (maponpaths (λ x, (x * _)%multmonoid)).
    unfold abmonoidfrac_lattice_fun.
    simpl ; unfold pr1carrier ; simpl.
    rewrite (assocax X (pr1 (pr2 x))).
    apply (maponpaths (λ x: X, op x _)).
    do 2 rewrite Hf.
    rewrite Hassoc.
    do 4 rewrite (assocax X).
    do 2 rewrite (commax X (pr1 (pr2 x))).
    reflexivity.
Qed.

Local Lemma isabsorb_abmonoidfrac_def :
  ∏ f g Hf Hg,
  isabsorb f g →
  isabsorb (X := abmonoidfrac X Y) (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                        (abmonoidfrac_lattice_def f Hf))
           (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                        (abmonoidfrac_lattice_def g Hg)).
Proof.
  intros f g Hf Hg Habsorb.
  simple refine (setquotuniv2prop _ (λ x y, (_ x (_ x y) = x) ,, _) _).
  - apply (setproperty (abmonoidfrac X Y)).
  - intros x y.
    simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    unfold abmonoidfrac_lattice_fun.
    apply (iscompsetquotpr (eqrelabmonoidfrac X Y)), hinhpr.
    exists (pr2 x).
    apply (maponpaths (λ x, (x * _)%multmonoid)).
    simpl ; unfold pr1carrier ; simpl.
    rewrite Hf, Hg, Hg.
    do 3 rewrite (assocax X (pr1 x)).
    rewrite (commax X (pr1 (pr2 y))).
    do 2 rewrite (assocax X (pr1 (pr2 x))).
    do 3 rewrite (commax X (pr1 (pr2 x))).
    apply Habsorb.
Qed.

(** definition of abmonoidfrac_lattice *)

Definition abmonoidfrac_min : binop (abmonoidfrac X Y) :=
  setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
              (abmonoidfrac_lattice_def min Hmin).
Definition abmonoidfrac_max : binop (abmonoidfrac X Y) :=
  setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
              (abmonoidfrac_lattice_def max Hmax).

Lemma iscomm_abmonoidfrac_min :
  iscomm abmonoidfrac_min.
Proof.
  apply iscomm_abmonoidfrac_def.
  apply Hmin_comm.
Qed.

Lemma isassoc_abmonoidfrac_min :
  isassoc abmonoidfrac_min.
Proof.
  apply isassoc_abmonoidfrac_def.
  apply Hmin_assoc.
Qed.

Lemma iscomm_abmonoidfrac_max :
  iscomm abmonoidfrac_max.
Proof.
  apply iscomm_abmonoidfrac_def.
  apply Hmax_comm.
Qed.

Lemma isassoc_abmonoidfrac_max :
  isassoc abmonoidfrac_max.
Proof.
  apply isassoc_abmonoidfrac_def.
  apply Hmax_assoc.
Qed.

Lemma isabsorb_abmonoidfrac_max_min :
  isabsorb abmonoidfrac_max abmonoidfrac_min.
Proof.
  apply isabsorb_abmonoidfrac_def.
  apply Hmax_min.
Qed.

Lemma isabsorb_abmonoidfrac_min_max :
  isabsorb abmonoidfrac_min abmonoidfrac_max.
Proof.
  apply isabsorb_abmonoidfrac_def.
  apply Hmin_max.
Qed.

End abmonoidfrac_lattice.

Lemma abmonoidfrac_islatticeop (X : abmonoid) (Y : @submonoid X) (lat : lattice X) :
  ∏ (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op),
  islatticeop (abmonoidfrac_min X Y Hmin) (abmonoidfrac_max X Y Hmax).
Proof.
  intros Hmin Hmax.
  repeat split.
  - apply isassoc_abmonoidfrac_min, isassoc_Lmin.
  - apply iscomm_abmonoidfrac_min, iscomm_Lmin.
  - apply isassoc_abmonoidfrac_max, isassoc_Lmax.
  - apply iscomm_abmonoidfrac_max, iscomm_Lmax.
  - apply isabsorb_abmonoidfrac_min_max, Lmin_absorb.
  - apply isabsorb_abmonoidfrac_max_min, Lmax_absorb.
Qed.

Definition abmonoidfrac_lattice (X : abmonoid) (Y : @submonoid X) (lat : lattice X)
           (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op) : lattice (abmonoidfrac X Y).
Proof.
  exists (abmonoidfrac_min X Y Hmin).
  exists (abmonoidfrac_max X Y Hmax).
  apply abmonoidfrac_islatticeop.
Defined.

Lemma ispartbinophrel_Lle (X : abmonoid) (Y : @submonoid X) (lat : lattice X)
      (Hmin : ispartrdistr Y (Lmin lat) op) :
  ispartbinophrel Y (Lle lat).
Proof.
  split.
  - intros a b c Yc.
    rewrite !(commax _ c).
    unfold Lle ; rewrite <- (Hmin _ _ (c,,Yc)).
    apply (maponpaths (λ x, op x _)).
  - intros a b c Yc.
    unfold Lle ; rewrite <- (Hmin _ _ (c,,Yc)).
    apply (maponpaths (λ x, op x _)).
Qed.

Lemma abmonoidfrac_Lle_1 (X : abmonoid) (Y : @submonoid X) (lat : lattice X)
      (Hmin : ispartrdistr _ (Lmin lat) op) :
  ∏ (x y : abmonoiddirprod X _),
  abmonoidfracrel X Y (ispartbinophrel_Lle X Y lat Hmin)
                  (setquotpr (binopeqrelabmonoidfrac X Y) x)
                  (setquotpr (binopeqrelabmonoidfrac X Y) y) →
  abmonoidfrac_min X Y Hmin (setquotpr (binopeqrelabmonoidfrac X Y) x)
                   (setquotpr (binopeqrelabmonoidfrac X Y) y) =
  setquotpr (binopeqrelabmonoidfrac X Y) x.
Proof.
  intros x y.
  unfold abmonoidfracrel, quotrel, abmonoidfrac_min.
  rewrite setquotuniv2comm, setquotfun2comm.
  intros H.
  apply iscompsetquotpr.
  revert H.
  apply hinhfun.
  intros c.
  exists (pr1 c).
  simpl in c |- *.
  rewrite (assocax X), (commax _ _ (pr1 (pr1 c))), <- (assocax X).
  rewrite Hmin.
  refine (pathscomp0 _ _).
  refine (maponpaths (λ x, x * _) _).
  apply (pr2 c).
  do 3 rewrite (assocax X) ;
    apply maponpaths.
  do 2 rewrite commax, assocax.
  apply pathsinv0, assocax.
Qed.
Lemma abmonoidfrac_Lle_2 (X : abmonoid) (Y : @submonoid X) (lat : lattice X)
      (Hmin : ispartrdistr _ (Lmin lat) op) :
  ∏ (x y : abmonoiddirprod X _),
  abmonoidfrac_min X Y Hmin (setquotpr (binopeqrelabmonoidfrac X Y) x)
                   (setquotpr (binopeqrelabmonoidfrac X Y) y) =
  setquotpr (binopeqrelabmonoidfrac X Y) x
  → abmonoidfracrel X Y (ispartbinophrel_Lle X Y lat Hmin)
                    (setquotpr (binopeqrelabmonoidfrac X Y) x)
                    (setquotpr (binopeqrelabmonoidfrac X Y) y).
Proof.
  intros x y.
  unfold abmonoidfracrel, quotrel, abmonoidfrac_min.
  rewrite setquotuniv2comm, setquotfun2comm.
  intros H.
  generalize (invmap (weqpathsinsetquot _ _ _) H).
  apply hinhfun.
  simpl.
  intros c.
  exists (pr2 x * pr1 c).
  rewrite <- Hmin.
  change (pr1 (pr2 x * pr1 c))%multmonoid
  with (pr1 (pr2 x) * pr1 (pr1 c))%multmonoid.
  rewrite <- assocax.
  refine (pathscomp0 _ _).
  apply (pr2 c).
  do 3 rewrite (assocax X) ;
    apply maponpaths.
  rewrite commax, assocax.
  apply maponpaths.
  apply commax.
Qed.

Lemma abmonoidfrac_Lle (X : abmonoid) (Y : @submonoid X) (lat : lattice X)
      (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op) :
  ∏ x y : abmonoidfrac X Y, abmonoidfracrel X Y (ispartbinophrel_Lle X Y lat Hmin) x y <-> Lle (abmonoidfrac_lattice X Y lat Hmin Hmax) x y.
Proof.
  simple refine (setquotuniv2prop _ (λ x y, _ ,, _) _).
  - apply isapropdirprod ;
    apply isapropimpl, propproperty.
  - intros x y.
    split.
    + apply abmonoidfrac_Lle_1.
    + apply abmonoidfrac_Lle_2.
Qed.

(** *** lattice with a strong order in [abmonoidfrac] *)

Section abmonoidfrac_latticewithgt.

Context (X : abmonoid)
        (Y : @submonoid X)
        (lat : lattice X)
        (gt : StrongOrder X)
        (Hnotgtle : ∏ x y : X, ¬ gt x y → Lle lat x y)
        (Hlenotgt : ∏ x y : X, Lle lat x y → ¬ gt x y)
        (Hgtmin : ∏ x y z : X, gt x z → gt y z → gt (Lmin lat x y) z)
        (Hgtmax : ∏ x y z : X, gt z x → gt z y → gt z (Lmax lat x y))

        (Hgt : ispartbinophrel Y gt)
        (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
        (Hmin : ispartrdistr Y (Lmin lat) op)
        (Hmax : ispartrdistr Y (Lmax lat) op).

Lemma abmonoidfrac_notgtle :
  ∏ (x y : abmonoidfrac X Y),
  ¬ (StrongOrder_abmonoidfrac Y gt Hgt) x y
  → Lle (abmonoidfrac_lattice X Y lat Hmin Hmax) x y.
Proof.
  simple refine (setquotuniv2prop (eqrelabmonoidfrac X Y) (λ _ _, _ ,, _) _).
  - apply isapropimpl, propproperty.
  - intros x y H.
    apply abmonoidfrac_Lle.
    unfold abmonoidfracrel, quotrel.
    rewrite setquotuniv2comm.
    apply hinhpr.
    exists (pr2 x).
    apply Hnotgtle.
    intros H0 ; apply H.
    change (abmonoidfracrel X Y Hgt
                            (setquotpr (eqrelabmonoidfrac X Y) x)
                            (setquotpr (eqrelabmonoidfrac X Y) y)).
    unfold abmonoidfracrel, quotrel.
    rewrite setquotuniv2comm.
    apply hinhpr.
    exists (pr2 x).
    exact H0.
Qed.

Lemma abmonoidfrac_lenotgt :
  ∏ (x y : abmonoidfrac X Y),
  Lle (abmonoidfrac_lattice X Y lat Hmin Hmax) x y
  → ¬ (StrongOrder_abmonoidfrac Y gt Hgt) x y.
Proof.
  simple refine (setquotuniv2prop (eqrelabmonoidfrac X Y) (λ _ _, _ ,, _) _).
  + apply isapropimpl, isapropimpl, isapropempty.
  + intros x y H.
    apply (pr2 (abmonoidfrac_Lle _ _ _ _ _ _ _)) in H.
    change (abmonoidfracrel X Y Hgt
                            (setquotpr (eqrelabmonoidfrac X Y) x)
                            (setquotpr (eqrelabmonoidfrac X Y) y) → ∅).
    revert H.
    unfold abmonoidfracrel, quotrel.
    do 2 rewrite setquotuniv2comm.
    apply (hinhuniv2 (P := make_hProp _ isapropempty)).
    intros c c'.
    refine (Hlenotgt _ _ _ _).
    2: apply (pr2 c').
    unfold Lle.
    rewrite <- Hmin.
    apply (maponpaths (λ x, op x _)).
    apply (Hop (pr1 c)).
    rewrite Hmin.
    apply (pr2 c).
Qed.

Lemma abmonoidfrac_gtmin :
  ∏ (x y z : abmonoidfrac X Y),
  (StrongOrder_abmonoidfrac Y gt Hgt) x z
  → (StrongOrder_abmonoidfrac Y gt Hgt) y z
  → (StrongOrder_abmonoidfrac Y gt Hgt)
      (Lmin (abmonoidfrac_lattice X Y lat Hmin Hmax) x y) z.
Proof.
  simple refine (setquotuniv3prop (eqrelabmonoidfrac X Y) (λ _ _ _, _ ,, _) _).
  - apply isapropimpl, isapropimpl, propproperty.
  - intros x y z.
    change (abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) x) (setquotpr (eqrelabmonoidfrac X Y) z)
            → abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) y) (setquotpr (eqrelabmonoidfrac X Y) z)
            → abmonoidfracrel X Y Hgt (abmonoidfrac_min X Y Hmin (setquotpr (eqrelabmonoidfrac X Y) x) (setquotpr (eqrelabmonoidfrac X Y) y)) (setquotpr (eqrelabmonoidfrac X Y) z)).
    unfold abmonoidfrac_min, abmonoidfracrel, quotrel.
    rewrite setquotfun2comm ;
      do 3 rewrite setquotuniv2comm.
    apply hinhfun2.
    intros cx cy.
    unfold abmonoidfrac_lattice_fun.
    simpl.
    exists (@op Y (pr1 cx) (pr1 cy)).
    do 2 rewrite Hmin.
    apply Hgtmin.
    + change (gt (pr1 x * pr1 (pr2 y) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
                 (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (assocax X (pr1 x)).
      rewrite (commax X (pr1 (pr2 y))).
      rewrite <- (assocax X (pr1 x)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      generalize (commax X (pr1 (pr2 y)) (pr1 (pr1 cx) * pr1 (pr1 cy))).
      intros ->.
      do 2 rewrite <- (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 y)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cy)).
      apply (pr2 cx).
    + change (gt (pr1 y * pr1 (pr2 x) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
                 (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (commax X (pr1 (pr1 cx))).
      rewrite (assocax X (pr1 y)).
      do 2 rewrite (commax X (pr1 (pr2 x))).
      rewrite <- (assocax X (pr1 y)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      rewrite (commax X (pr1 (pr2 x))).
      do 2 rewrite <- (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 x)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cx)).
      apply (pr2 cy).
Qed.

Lemma abmonoidfrac_gtmax :
  ∏ (x y z : abmonoidfrac X Y),
  (StrongOrder_abmonoidfrac Y gt Hgt) z x
  → (StrongOrder_abmonoidfrac Y gt Hgt) z y
    → (StrongOrder_abmonoidfrac Y gt Hgt) z
         (Lmax (abmonoidfrac_lattice X Y lat Hmin Hmax) x y).
Proof.
  simple refine (setquotuniv3prop (eqrelabmonoidfrac X Y) (λ _ _ _, _ ,, _) _).
  - apply isapropimpl, isapropimpl, propproperty.
  - intros x y z.
    change (abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) z) (setquotpr (eqrelabmonoidfrac X Y) x)
            → abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) z) (setquotpr (eqrelabmonoidfrac X Y) y)
            → abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) z) (abmonoidfrac_max X Y Hmax (setquotpr (eqrelabmonoidfrac X Y) x) (setquotpr (eqrelabmonoidfrac X Y) y))).
    unfold abmonoidfrac_max, abmonoidfracrel, quotrel.
    rewrite setquotfun2comm ;
      do 3 rewrite setquotuniv2comm.
    apply hinhfun2.
    intros cx cy.
    unfold abmonoidfrac_lattice_fun.
    change (∑ c0 : Y,
  gt
    (pr1 z * pr1 (pr2 x * pr2 y) * pr1 c0)
    (Lmax lat (pr1 x * pr1 (pr2 y)) (pr1 y * pr1 (pr2 x)) *
     pr1 (pr2 z) * pr1 c0)).
    exists (@op Y (pr1 cx) (pr1 cy)).
    do 2 rewrite Hmax.
    apply Hgtmax.
    + change (gt (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
    (pr1 x * pr1 (pr2 y) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (assocax X (pr1 x)).
      rewrite (commax X (pr1 (pr2 y))).
      rewrite <- (assocax X (pr1 x)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      generalize (commax X (pr1 (pr2 y)) (pr1 (pr1 cx) * pr1 (pr1 cy))).
      intros ->.
      do 2 rewrite <- (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 y)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cy)).
      apply (pr2 cx).
    + change (gt (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
    (pr1 y * pr1 (pr2 x) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (commax X (pr1 (pr1 cx))).
      rewrite (assocax X (pr1 y)).
      do 2 rewrite (commax X (pr1 (pr2 x))).
      rewrite <- (assocax X (pr1 y)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      rewrite (commax X (pr1 (pr2 x))).
      do 2 rewrite <- (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 x)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cx)).
      apply (pr2 cy).
Qed.

End abmonoidfrac_latticewithgt.

Definition abmonoidfrac_latticewithgt (X : abmonoid) (Y : @submonoid X) (lat : latticewithgt X)
           (Hgt : ispartbinophrel Y (Lgt lat))
           (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
           (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op) : latticewithgt (abmonoidfrac X Y).
Proof.
  simple refine (tpair _ _ _).
  refine (abmonoidfrac_lattice _ _ _ _ _).
  exact Hmin.
  exact Hmax.
  simple refine (tpair _ _ _).
  simple refine (StrongOrder_abmonoidfrac _ _ _).
  apply (Lgt lat).
  apply Hgt.
  split ; split.
  - apply abmonoidfrac_notgtle.
    apply notLgt_Lle.
  - apply abmonoidfrac_lenotgt.
    apply Lle_notLgt.
    apply Hop.
  - apply abmonoidfrac_gtmin.
    apply Lmin_Lgt.
  - apply abmonoidfrac_gtmax.
    apply Lmax_Lgt.
Defined.

(** *** lattice with a decidable order in [abmonoidfrac] *)

Lemma istotal_Lle_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (lat : lattice X) (is' : istotal (Lle lat))
           (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op) :
  istotal (Lle (abmonoidfrac_lattice X Y lat Hmin Hmax)).
Proof.
  refine (istotallogeqf _ _).
  - apply abmonoidfrac_Lle.
  - apply istotalabmonoidfracrel, is'.
Qed.
Lemma isdecrel_Lle_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (lat : lattice X) (is' : isdecrel (Lle lat))
           (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
           (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op) :
  isdecrel (Lle (abmonoidfrac_lattice X Y lat Hmin Hmax)).
Proof.
  refine (isdecrellogeqf _ _).
  - apply abmonoidfrac_Lle.
  - apply isdecabmonoidfracrel.
    split.
    + clear -Hmin Hop.
      intros x y z Hz ;
        rewrite !(commax X z) ;
        unfold Lle ;
        rewrite <- (Hmin _ _ (z,,Hz)) ;
        apply Hop.
    + clear -Hmin Hop.
      intros x y z Hz ;
        unfold Lle ;
        rewrite <- (Hmin _ _ (z,,Hz)) ;
        apply Hop.
    + apply is'.
Qed.

Definition abmonoidfrac_latticedec {X : abmonoid} (Y : @submonoid X) (lat : latticedec X)
           (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
           (Hmin : ispartrdistr Y (Lmin lat) op) (Hmax : ispartrdistr Y (Lmax lat) op) :
  latticedec (abmonoidfrac X Y).
Proof.
  exists (abmonoidfrac_lattice X Y lat Hmin Hmax).
  split.
  - apply istotal_Lle_abmonoidfrac.
    apply istotal_latticedec.
  - apply isdecrel_Lle_abmonoidfrac.
    + apply isdecrel_latticedec.
    + apply Hop.
Defined.

Close Scope multmonoid.

Section hProp_lattice.

Definition hProp_lattice : lattice (hProp,,isasethProp).
Proof.
use mklattice.
- intros P Q; exact (P ∧ Q).
- simpl; intros P Q; exact (P ∨ Q).
- repeat split.
  + intros P Q R; apply isassoc_hconj.
  + intros P Q; apply iscomm_hconj.
  + intros P Q R; apply isassoc_hdisj.
  + intros P Q; apply iscomm_hdisj.
  + intros P Q; apply hconj_absorb_hdisj.
  + intros P Q; apply hdisj_absorb_hconj.
Defined.

Definition hProp_bounded_lattice : bounded_lattice (hProp,,isasethProp).
Proof.
use mkbounded_lattice.
- exact hProp_lattice.
- exact hfalse.
- exact htrue.
- split.
  + intros P; apply hfalse_hdisj.
  + intros P; apply htrue_hconj.
Defined.

End hProp_lattice.
