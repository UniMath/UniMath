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
- le := λ (x y : X), min is x y = x

Lattice with a strict order:
A lattice with a strict order gt is lattice such that:
- ∏ (x y : X), (¬ gt x y) <-> le x y
- ∏ x y z : X, gt x z → gt y z → gt (min x y) z
- ∏ x y z : X, gt z x → gt z y → gt z (max is x y)

Lattice with a total and decidable order:
- le is total and decidable
- it is a lattice with a strong order *)

(**
Lattice in an abelian monoid:
- compatibility and cancelation of addition for le

Truncated minus is a lattice:
- a function minus such that: ∏ (x y : X), (minus x y) + y = max x y *)

Require Export UniMath.Algebra.Monoids_and_Groups.
Import MultNotation.

Require Import UniMath.MoreFoundations.All.

Unset Automatic Introduction.

(** ** Strong Order *)
(* todo : move it into UniMath.Foundations.Sets *)

Definition isStrongOrder {X : UU} (R : hrel X) := istrans R × iscotrans R × isirrefl R.
Definition StrongOrder (X : UU) := ∑ R : hrel X, isStrongOrder R.
Definition pairStrongOrder {X : UU} (R : hrel X) (is : isStrongOrder R) : StrongOrder X :=
  tpair (λ R : hrel X, isStrongOrder R ) R is.
Definition pr1StrongOrder {X : UU} : StrongOrder X → hrel X := pr1.
Coercion  pr1StrongOrder : StrongOrder >-> hrel.

Section so_pty.

Context {X : UU}.
Context (R : StrongOrder X).

Definition istrans_StrongOrder : istrans R :=
  pr1 (pr2 R).
Definition iscotrans_StrongOrder : iscotrans R :=
  pr1 (pr2 (pr2 R)).
Definition isirrefl_StrongOrder : isirrefl R :=
  pr2 (pr2 (pr2 R)).
Definition isasymm_StrongOrder : isasymm R :=
  istransandirrefltoasymm
    istrans_StrongOrder
    isirrefl_StrongOrder.

End so_pty.

Lemma isStrongOrder_setquot {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L → isStrongOrder (quotrel is).
Proof.
  intros X R L is H.
  split ; [ | split].
  - apply istransquotrel, (pr1 H).
  - apply iscotransquotrel, (pr1 (pr2 H)).
  - apply isirreflquotrel, (pr2 (pr2 H)).
Qed.
Definition StrongOrder_setquot {X : UU} {R : eqrel X} {L : StrongOrder X} (is : iscomprelrel R L) : StrongOrder (setquot R) :=
  quotrel is,, isStrongOrder_setquot is (pr2 L).

(** ** Definition *)

Definition latticeop {X : hSet} (min max : binop X) :=
  ((isassoc min) × (iscomm min))
    × ((isassoc max) × (iscomm max))
    × (∏ x y : X, min x (max x y) = x)
    × (∏ x y : X, max x (min x y) = x).
Definition lattice (X : hSet) := ∑ min max : binop X, latticeop min max.

Definition mklattice {X : hSet} {min max : binop X} : latticeop min max → lattice X :=
  λ (is : latticeop min max), min,, max ,, is.

Definition Lmin {X : hSet} (is : lattice X) : binop X := pr1 is.
Definition Lmax {X : hSet} (is : lattice X) : binop X := pr1 (pr2 is).

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
        (is : lattice X).

Definition isassoc_Lmin : isassoc (Lmin is) :=
  pr1 (pr1 (pr2 (pr2 is))).
Definition iscomm_Lmin : iscomm (Lmin is) :=
  pr2 (pr1 (pr2 (pr2 is))).
Definition isassoc_Lmax : isassoc (Lmax is) :=
  pr1 (pr1 (pr2 (pr2 (pr2 is)))).
Definition iscomm_Lmax : iscomm (Lmax is) :=
  pr2 (pr1 (pr2 (pr2 (pr2 is)))).
Definition Lmin_absorb :
  ∏ x y : X, Lmin is x (Lmax is x y) = x :=
  pr1 (pr2 (pr2 (pr2 (pr2 is)))).
Definition Lmax_absorb :
  ∏ x y : X, Lmax is x (Lmin is x y) = x :=
  pr2 (pr2 (pr2 (pr2 (pr2 is)))).

Lemma Lmin_id :
  ∏ x : X, Lmin is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmin is x (Lmax is x (Lmin is x x)))).
  - apply maponpaths, pathsinv0, Lmax_absorb.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  ∏ x : X, Lmax is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmax is x (Lmin is x (Lmax is x x)))).
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
intros x.
now rewrite <- (islunit_Lmax_Lbot x), Lmin_absorb.
Qed.

Lemma Lmax_Ltop (x : X) : Lmax l (Ltop l) x = Ltop l.
Proof.
intros x.
now rewrite <- (islunit_Lmin_Ltop x), Lmax_absorb.
Qed.

End bounded_lattice_pty.

(** ** Partial order in a lattice *)

(** [Lle] *)

Definition Lle {X : hSet} (is : lattice X) : hrel X :=
  λ (x y : X), hProppair (Lmin is x y = x) ((pr2 X) (Lmin is x y) x).

Section lattice_le.

Context {X : hSet}
        (is : lattice X).

Definition isrefl_Lle : isrefl (Lle is) :=
  Lmin_id is.
Lemma isantisymm_Lle :
  isantisymm (Lle is).
Proof.
  intros x y Hxy Hyx.
  apply pathscomp0 with (1 := pathsinv0 Hxy).
  apply pathscomp0 with (2 := Hyx).
  apply iscomm_Lmin.
Qed.
Lemma istrans_Lle :
  istrans (Lle is).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite !isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma isPartialOrder_Lle :
  isPartialOrder (Lle is).
Proof.
  split ; [ split | ].
  - exact istrans_Lle.
  - exact isrefl_Lle.
  - exact isantisymm_Lle.
Qed.

Lemma Lmin_le_l :
  ∏ x y : X, Lle is (Lmin is x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  ∏ x y : X, Lle is (Lmin is x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmin_le_case :
  ∏ x y z : X, Lle is z x → Lle is z y → Lle is z (Lmin is x y).
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
  ∏ x y : X, Lle is x (Lmax is x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  ∏ x y : X, Lle is y (Lmax is x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.
Lemma Lmax_le_case :
  isrdistr (Lmax is) (Lmin is)
  → ∏ x y z : X, Lle is x z → Lle is y z → Lle is (Lmax is x y) z.
Proof.
  intros H x y z <- <-.
  rewrite <- H.
  apply Lmin_le_r.
Qed.

Lemma Lmin_le_eq_l :
  ∏ x y : X, Lle is x y → Lmin is x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_le_eq_r :
  ∏ x y : X, Lle is y x → Lmin is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_le_eq_l :
  ∏ x y : X, Lle is y x → Lmax is x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_le_eq_r :
  ∏ x y : X, Lle is x y → Lmax is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_le_eq_l.
Qed.

End lattice_le.

(** [Lge] *)

Definition Lge {X : hSet} (is : lattice X) : hrel X :=
  λ x y : X, Lle is y x.

Section Lge_pty.

Context {X : hSet}
        (is : lattice X).

Definition isrefl_Lge : isrefl (Lge is) :=
  isrefl_Lle is.
Lemma isantisymm_Lge :
  isantisymm (Lge is).
Proof.
  intros x y Hle Hge.
  apply (isantisymm_Lle is).
  exact Hge.
  exact Hle.
Qed.
Lemma istrans_Lge :
  istrans (Lge is).
Proof.
  intros x y z Hxy Hyz.
  apply (istrans_Lle is) with y.
  exact Hyz.
  exact Hxy.
Qed.
Lemma isPartialOrder_Lge :
  isPartialOrder (Lge is).
Proof.
  split ; [ split | ].
  - exact istrans_Lge.
  - exact isrefl_Lge.
  - exact isantisymm_Lge.
Qed.

Definition Lmin_ge_l :
  ∏ (x y : X), Lge is x (Lmin is x y) :=
  Lmin_le_l is.
Definition Lmin_ge_r :
  ∏ (x y : X), Lge is y (Lmin is x y) :=
  Lmin_le_r is.
Definition Lmin_ge_case :
  ∏ (x y z : X),
  Lge is x z → Lge is y z → Lge is (Lmin is x y) z :=
  Lmin_le_case is.

Definition Lmax_ge_l :
  ∏ (x y : X), Lge is (Lmax is x y) x :=
  Lmax_le_l is.
Definition Lmax_ge_r :
  ∏ (x y : X), Lge is (Lmax is x y) y :=
  Lmax_le_r is.
Definition Lmax_ge_case :
  isrdistr (Lmax is) (Lmin is)
  → ∏ x y z : X, Lge is z x → Lge is z y → Lge is z (Lmax is x y) :=
  Lmax_le_case is.

Definition Lmin_ge_eq_l :
  ∏ (x y : X), Lge is y x → Lmin is x y = x :=
  Lmin_le_eq_l is.
Definition Lmin_ge_eq_r :
  ∏ (x y : X), Lge is x y → Lmin is x y = y :=
  Lmin_le_eq_r is.

Definition Lmax_ge_eq_l :
  ∏ (x y : X), Lge is x y → Lmax is x y = x :=
  Lmax_le_eq_l is.
Definition Lmax_ge_eq_r :
  ∏ (x y : X), Lge is y x → Lmax is x y = y :=
  Lmax_le_eq_r is.

End Lge_pty.

(** ** Lattice with a strong order *)

Definition latticewithgtrel {X : hSet} (is : lattice X) (gt : StrongOrder X) :=
  (∏ x y : X, (¬ (gt x y)) <-> Lle is x y)
    × (∏ x y z : X, gt x z → gt y z → gt (Lmin is x y) z)
    × (∏ x y z : X, gt z x → gt z y → gt z (Lmax is x y)).

Definition latticewithgt (X : hSet) :=
  ∑ (is : lattice X) (gt : StrongOrder X), latticewithgtrel is gt.

Definition lattice_latticewithgt {X : hSet} : latticewithgt X → lattice X :=
  pr1.
Coercion lattice_latticewithgt : latticewithgt >-> lattice.

(** [Lgt] *)

Definition Lgt {X : hSet} (is : latticewithgt X) : StrongOrder X :=
  pr1 (pr2 is).

Section latticewithgt_pty.

Context {X : hSet}
        (is : latticewithgt X).

Definition notLgt_Lle :
  ∏ x y : X, (¬ Lgt is x y) → Lle is x y :=
  λ x y : X, pr1 (pr1 (pr2 (pr2 is)) x y).
Definition Lle_notLgt :
  ∏ x y : X, Lle is x y → ¬ Lgt is x y :=
  λ x y : X, pr2 (pr1 (pr2 (pr2 is)) x y).

Definition isirrefl_Lgt : isirrefl (Lgt is) :=
  isirrefl_StrongOrder (Lgt is).
Definition istrans_Lgt : istrans (Lgt is) :=
  istrans_StrongOrder (Lgt is).
Definition iscotrans_Lgt : iscotrans (Lgt is) :=
  iscotrans_StrongOrder (Lgt is).
Definition isasymm_Lgt : isasymm (Lgt is) :=
  isasymm_StrongOrder (Lgt is).

Lemma Lgt_Lge :
  ∏ x y : X, Lgt is x y → Lge is x y.
Proof.
  intros x y H.
  apply notLgt_Lle.
  intro H0.
  eapply isasymm_Lgt.
  exact H.
  exact H0.
Qed.

Lemma istrans_Lgt_Lge :
  ∏ x y z : X, Lgt is x y → Lge is y z → Lgt is x z.
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
  ∏ x y z : X, Lge is x y → Lgt is y z → Lgt is x z.
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
  ∏ x y z : X, Lgt is x z → Lgt is y z → Lgt is (Lmin is x y) z :=
  pr1 (pr2 (pr2 (pr2 is))).

Definition Lmax_Lgt :
  ∏ x y z : X, Lgt is z x → Lgt is z y → Lgt is z (Lmax is x y) :=
  pr2 (pr2 (pr2 (pr2 is))).

End latticewithgt_pty.

(** ** Lattice with a total order *)

Definition latticedec (X : hSet) :=
  ∑ is : lattice X, istotal (Lle is) × (isdecrel (Lle is)).
Definition lattice_latticedec {X : hSet} (is : latticedec X) : lattice X :=
  pr1 is.
Coercion lattice_latticedec : latticedec >-> lattice.
Definition istotal_latticedec {X : hSet} (is : latticedec X) : istotal (Lle is) :=
  pr1 (pr2 is).
Definition isdecrel_latticedec {X : hSet} (is : latticedec X) : isdecrel (Lle is) :=
  pr2 (pr2 is).

Section latticedec_pty.

Context {X : hSet}
        (is : latticedec X).

Lemma Lmin_case_strong :
  ∏ (P : X → UU) (x y : X),
  (Lle is x y → P x) → (Lle is y x → P y) → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_latticedec is x y).
  apply sumofmaps ; intros H.
  - rewrite Lmin_le_eq_l.
    apply Hx, H.
    exact H.
  - enough (H0 : Lle is y x).
    + rewrite Lmin_le_eq_r.
      apply Hy, H0.
      exact H0.
    + generalize (istotal_latticedec is x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmin_case :
  ∏ (P : X → UU) (x y : X),
  P x → P y → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma Lmax_case_strong :
  ∏ (P : X → UU) (x y : X),
  (Lle is y x → P x) → (Lle is x y → P y) → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_latticedec is x y).
  apply sumofmaps ; intros H.
  - rewrite Lmax_le_eq_r.
    apply Hy, H.
    exact H.
  - enough (H0 : Lle is y x).
    + rewrite Lmax_le_eq_l.
      apply Hx, H0.
      exact H0.
    + generalize (istotal_latticedec is x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmax_case :
  ∏ (P : X → UU) (x y : X),
  P x → P y → P (Lmax is x y).
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
        (is : latticedec X).

Definition latticedec_gt_rel : hrel X :=
  λ x y, hneg (Lle is x y).

Lemma latticedec_gt_ge :
  ∏ x y : X, latticedec_gt_rel x y → Lge is x y.
Proof.
  intros x y Hxy.
  generalize (istotal_latticedec is x y).
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
  induction (isdecrel_latticedec is x y) as [Hxy | Hyx].
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
  split ; [ | split].
  - apply istrans_latticedec_gt_rel.
  - apply iscotrans_latticedec_gt_rel.
  - intros x Hx.
    simple refine (Hx _).
    apply isrefl_Lle.
Defined.

Lemma latticedec_notgtle :
  ∏ (x y : X), ¬ latticedec_gt_so x y → Lle is x y.
Proof.
  intros x y H.
  induction (isdecrel_latticedec is x y) as [H0 | H0].
  + exact H0.
  + apply fromempty, H.
    exact H0.
Qed.

Lemma latticedec_lenotgt :
  ∏ (x y : X), Lle is x y → ¬ latticedec_gt_so x y.
Proof.
  intros x y H H0.
  simple refine (H0 _).
  exact H.
Qed.

Lemma latticedec_gtmin :
  ∏ (x y z : X),
  latticedec_gt_so x z
  → latticedec_gt_so y z → latticedec_gt_so (Lmin is x y) z.
Proof.
  intros x y z Hxz Hyz.
  apply (Lmin_case is (λ t : X, latticedec_gt_so t z)).
  - exact Hxz.
  - exact Hyz.
Qed.

Lemma latticedec_gtmax :
  ∏ (x y z : X),
  latticedec_gt_so z x
  → latticedec_gt_so z y → latticedec_gt_so z (Lmax is x y).
Proof.
  intros x y z Hxz Hyz.
  apply (Lmax_case is (latticedec_gt_so z)).
  - exact Hxz.
  - exact Hyz.
Qed.

Definition latticedec_gt : latticewithgt X.
Proof.
  exists (lattice_latticedec is).
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
Import UniMath.Algebra.Monoids_and_Groups.AddNotation.

Section lattice_abmonoid.

Context {X : abmonoid}
        (is : lattice X)
        (is0 : ∏ x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmin is) op).

Lemma op_le_r :
  ∏ k x y : X, Lle is x y → Lle is (x + k) (y + k).
Proof.
  intros k x y H.
  unfold Lle ; simpl.
  now rewrite <- is2, H.
Qed.
Lemma op_le_r' :
  ∏ k x y : X, Lle is (x + k) (y + k) → Lle is x y.
Proof.
  intros k x y H.
  apply (is0 k).
  now rewrite is2, H.
Qed.

End lattice_abmonoid.

(** ** Truncated minus *)

Definition istruncminus {X : abmonoid} (is : lattice X) (minus : binop X) :=
  ∏ x y : X, minus x y + y = Lmax is x y.
Lemma isaprop_istruncminus {X : abmonoid} (is : lattice X) (minus : binop X) :
  isaprop (istruncminus is minus).
Proof.
  intros X is minus.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply (pr2 (pr1 (pr1 X))).
Qed.

Definition extruncminus {X : abmonoid} (is : lattice X) :=
  ∑ minus : binop X, istruncminus is minus.
Lemma isaprop_extruncminus {X : abmonoid} (is : lattice X)
      (Hop : ∏ x y z : X, y + x = z + x → y = z) :
  isaprop (extruncminus is).
Proof.
  intros X is Hop.
  intros minus1 minus2 ; simpl.
  rewrite (subtypeEquality' (s := minus1) (s' := minus2)).
  - apply iscontrloopsifisaset.
    apply isaset_total2.
    apply impred_isaset ; intros _.
    apply impred_isaset ; intros _.
    apply (pr2 (pr1 (pr1 X))).
    intros minus.
    apply isasetaprop.
    apply isaprop_istruncminus.
  - apply weqfunextsec ; intros x.
    apply weqfunextsec ; intros y.
    apply (Hop y).
    rewrite (pr2 minus1).
    apply pathsinv0, (pr2 minus2).
  - apply isaprop_istruncminus.
Qed.

Definition truncminus {X : abmonoid} {is : lattice X} (ex : extruncminus is) : binop X :=
  pr1 ex.

Lemma istruncminus_ex {X : abmonoid} {is : lattice X} (ex : extruncminus is) :
  ∏ x y : X, truncminus ex x y + y = Lmax is x y.
Proof.
  intros X is ex.
  apply (pr2 ex).
Qed.

Section truncminus_pty.

Context {X : abmonoid}
        {is : lattice X}
        (ex : extruncminus is)
        (is1 : ∏ x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmin is) (Lmax is))
        (is5 : isrdistr (Lmax is) (Lmin is)).

Lemma truncminus_0_r :
  ∏ x : X, truncminus ex x 0 = Lmax is x 0.
Proof.
  intros x.
  rewrite <- (runax _ (truncminus _ _ _)).
  apply (istruncminus_ex).
Qed.

Lemma truncminus_eq_0 :
  ∏ x y : X, Lle is x y → truncminus ex x y = 0.
Proof.
  intros x y H.
  apply (is1 y).
  rewrite istruncminus_ex, lunax.
  apply Lmax_le_eq_r, H.
Qed.

Lemma truncminus_0_l_ge0 :
  ∏ x : X, Lle is 0 x → truncminus ex 0 x = 0.
Proof.
  intros x Hx.
  apply truncminus_eq_0, Hx.
Qed.
Lemma truncminus_0_l_le0 :
  ∏ x : X, Lle is x 0 → truncminus ex 0 x + x = 0.
Proof.
  intros x Hx.
  rewrite istruncminus_ex.
  apply Lmax_le_eq_l, Hx.
Qed.

Lemma truncminus_ge_0 :
  ∏ x y : X, Lle is 0 (truncminus ex x y).
Proof.
  intros x y.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex, lunax.
  apply Lmax_ge_r.
Qed.

Lemma truncminus_le :
  ∏ x y : X,
          Lle is 0 x → Lle is 0 y
          → Lle is (truncminus ex x y) x.
Proof.
  intros x y Hx Hy.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex.
  apply Lmax_le_case.
  - apply is5.
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
  ∏ x y, Lle is 0 x → Lle is x y → truncminus ex y (truncminus ex y x) = x.
Proof.
  intros x y Hx Hxy.
  apply (is1 (truncminus ex y x)).
  rewrite (commax _ x), !istruncminus_ex.
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
  ∏ k x y : X, Lle is x y → Lle is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y <-.
  apply (is1 k).
  rewrite is3, !istruncminus_ex.
  rewrite is4, isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma truncminus_le_l :
  ∏ k x y : X, Lle is y x → Lle is (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (is1 y).
  rewrite is3, istruncminus_ex.
  apply (is1 x).
  rewrite is3, assocax, (commax _ y), <- assocax, istruncminus_ex.
  rewrite !is2, (commax _ y), <- is4, !(commax _ k), <- is3, H.
  reflexivity.
Qed.

Lemma truncminus_Lmax_l :
  ∏ (k x y : X),
  truncminus ex (Lmax is x y) k = Lmax is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is2, !istruncminus_ex.
  rewrite !isassoc_Lmax, (iscomm_Lmax _ k), isassoc_Lmax, Lmax_id.
  reflexivity.
Qed.
Lemma truncminus_Lmax_r :
  ∏ (k x y : X),
  Lle is (Lmin is (y + y) (x + x)) (x + y) →
  truncminus ex k (Lmax is x y) = Lmin is (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (is1 (Lmax is x y)).
  rewrite is3, istruncminus_ex.
  rewrite !(commax _ _ (Lmax _ _ _)), !is2.
  rewrite !(commax _ _ (truncminus _ _ _)), !istruncminus_ex.
  rewrite (iscomm_Lmax _ (_*_)%multmonoid (Lmax _ _ _)).
  rewrite !isassoc_Lmax, !(iscomm_Lmax _ k).
  rewrite <- is4.

  apply (is1 x).
  rewrite !is2, is3, !is2.
  rewrite assocax, (commax _ y x), <- assocax.
  rewrite istruncminus_ex, is2.

  apply (is1 y).
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
                     (Lmin is (y * y) (x * x) * k)%multmonoid).
  reflexivity.
  apply op_le_r.
  exact is3.
  exact H.
Qed.

Lemma truncminus_Lmin_l :
  ∏ k x y : X, truncminus ex (Lmin is x y) k = Lmin is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is3, !istruncminus_ex.
  apply is4.
Qed.

End truncminus_pty.

Lemma abgr_truncminus {X : abgr} (is : lattice X) :
  isrdistr (Lmax is) op →
  istruncminus (X := abgrtoabmonoid X) is (λ x y : X, Lmax is 0 (x + grinv X y)).
Proof.
  intros X is H x y.
  rewrite H, assocax, grlinvax, lunax, runax.
  apply iscomm_Lmax.
Qed.

Section truncminus_gt.

Context {X : abmonoid}
        (is : latticewithgt X)
        (ex : extruncminus is)
        (is0 : ∏ x y z : X, Lgt is y z → Lgt is (y + x) (z + x))
        (is1 : ∏ x y z : X, Lgt is (y + x) (z + x) → Lgt is y z).

Lemma truncminus_pos :
  ∏ x y : X, Lgt is x y → Lgt is (truncminus ex x y) 0.
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
  ∏ x y : X, Lgt is (truncminus ex x y) 0 → Lgt is x y.
Proof.
  intros x y Hgt.
  apply (is0 y) in Hgt.
  rewrite istruncminus_ex, lunax in Hgt.
  rewrite <- (Lmax_le_eq_l is x y).
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