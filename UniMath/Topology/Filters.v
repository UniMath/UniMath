(** * Results about Filters *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Subtypes.
Require Export UniMath.Topology.Prelim.
Require Import UniMath.MoreFoundations.PartA.

(** ** Definition of a Filter *)

Local Open Scope subtype.

Section Filter_def.

Context {X : UU}.
Context (F : hsubtype (hsubtype X)).

Definition isfilter_imply :=
  ∏ A B : hsubtype X, (A ⊆ B) → F A → F B.
Lemma isaprop_isfilter_imply : isaprop isfilter_imply.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropimpl.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition isfilter_finite_intersection :=
  ∏ (L : Sequence (hsubtype X)), (∏ n, F (L n)) → F (finite_intersection L).
Lemma isaprop_isfilter_finite_intersection :
  isaprop isfilter_finite_intersection.
Proof.
  apply impred_isaprop ; intros L.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition isfilter_htrue : hProp :=
  F (λ _ : X, htrue).

Definition isfilter_and :=
  ∏ A B : hsubtype X, F A → F B → F (λ x : X, A x ∧ B x).
Lemma isaprop_isfilter_and : isaprop isfilter_and.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropimpl.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition isfilter_notempty :=
  ∏ A : hsubtype X, F A → ∃ x : X, A x.
Lemma isaprop_isfilter_notempty :
  isaprop isfilter_notempty.
Proof.
  apply impred_isaprop ; intro A.
  apply isapropimpl.
  apply propproperty.
Qed.

Lemma isfilter_finite_intersection_htrue :
  isfilter_finite_intersection → isfilter_htrue.
Proof.
  intros Hand.
  unfold isfilter_htrue.
  rewrite <- finite_intersection_htrue.
  apply Hand.
  intros m.
  apply fromempty.
  generalize (pr2 m).
  now apply negnatlthn0.
Qed.

Lemma isfilter_finite_intersection_and :
  isfilter_finite_intersection → isfilter_and.
Proof.
  intros Hand A B Fa Fb.
  rewrite <- finite_intersection_and.
  apply Hand.
  intros m.
  induction m as [m Hm].
  induction m as [ | m _].
  - exact Fa.
  - exact Fb.
Qed.

Lemma isfilter_finite_intersection_carac :
  isfilter_htrue → isfilter_and
  → isfilter_finite_intersection.
Proof.
  intros Htrue Hand L.
  apply (pr2 (finite_intersection_hProp F)).
  split.
  - exact Htrue.
  - exact Hand.
Qed.

End Filter_def.

Definition isPreFilter {X : UU} (F : hsubtype (hsubtype X)) :=
  isfilter_imply F × isfilter_finite_intersection F.
Definition PreFilter (X : UU) :=
  ∑ (F : hsubtype (hsubtype X)), isPreFilter F.
Definition make_PreFilter {X : UU} (F : hsubtype (hsubtype X))
           (Himpl : isfilter_imply F)
           (Htrue : isfilter_htrue F)
           (Hand : isfilter_and F) : PreFilter X :=
  F,, Himpl,, isfilter_finite_intersection_carac F Htrue Hand.

Definition pr1PreFilter (X : UU) (F : PreFilter X) : (hsubtype X) → hProp := pr1 F.
Coercion pr1PreFilter : PreFilter >-> Funclass.

Definition isFilter {X : UU} (F : hsubtype (hsubtype X)) :=
  isPreFilter F × isfilter_notempty F.
Definition Filter (X : UU) := ∑ F : hsubtype (hsubtype X), isFilter F.
Definition pr1Filter (X : UU) (F : Filter X) : PreFilter X :=
  pr1 F,, pr1 (pr2 F).
Coercion pr1Filter : Filter >-> PreFilter.
Definition make_Filter {X : UU} (F : hsubtype (hsubtype X))
           (Himp : isfilter_imply F)
           (Htrue : isfilter_htrue F)
           (Hand : isfilter_and F)
           (Hempty : isfilter_notempty F) : Filter X :=
  F ,, (Himp ,, (isfilter_finite_intersection_carac F Htrue Hand)) ,, Hempty.

Lemma emptynofilter :
  ∏ F : hsubtype (hsubtype empty),
    ¬ isFilter F.
Proof.
  intros F Hf.
  generalize (isfilter_finite_intersection_htrue _ (pr2 (pr1 Hf))) ; intros Htrue.
  generalize (pr2 Hf _ Htrue).
  apply factor_through_squash.
  - apply isapropempty.
  - intros x.
    apply (pr1 x).
Qed.

Section PreFilter_pty.

Context {X : UU}.
Context (F : PreFilter X).

Lemma filter_imply :
  isfilter_imply F.
Proof.
  exact (pr1 (pr2 F)).
Qed.
Lemma filter_finite_intersection :
  isfilter_finite_intersection F.
Proof.
  exact (pr2 (pr2 F)).
Qed.
Lemma filter_htrue :
  isfilter_htrue F.
Proof.
  apply isfilter_finite_intersection_htrue.
  exact filter_finite_intersection.
Qed.
Lemma filter_and :
  isfilter_and F.
Proof.
  apply isfilter_finite_intersection_and.
  exact filter_finite_intersection.
Qed.

Lemma filter_forall :
  ∏ A : hsubtype X, (∏ x : X, A x) → F A.
Proof.
  intros A Ha.
  generalize filter_htrue.
  apply filter_imply.
  intros x _.
  now apply Ha.
Qed.

End PreFilter_pty.

Section Filter_pty.

Context {X : UU}.
Context (F : Filter X).

Lemma filter_notempty :
  isfilter_notempty F.
Proof.
  exact (pr2 (pr2 F)).
Qed.

Lemma filter_const :
  ∏ A : hProp, F (λ _ : X, A) → ¬ (¬ A).
Proof.
  intros A Fa Ha.
  generalize (filter_notempty _ Fa).
  apply factor_through_squash.
  - apply isapropempty.
  - intros x ; generalize (pr2 x); clear x.
    exact Ha.
Qed.

End Filter_pty.

Lemma isasetPreFilter (X : UU) : isaset (PreFilter X).
Proof.
  simple refine (isaset_carrier_subset (make_hSet _ _) (λ _, make_hProp _ _)).
  - apply impred_isaset ; intros _.
    apply isasethProp.
  - apply isapropdirprod.
    + apply isaprop_isfilter_imply.
    + apply isaprop_isfilter_finite_intersection.
Qed.

Lemma isasetFilter (X : UU) : isaset (Filter X).
Proof.
  simple refine (isaset_carrier_subset (make_hSet _ _) (λ _, make_hProp _ _)).
  - apply impred_isaset ; intros _.
    apply isasethProp.
  - apply isapropdirprod.
    + apply isapropdirprod.
      * apply isaprop_isfilter_imply.
      * apply isaprop_isfilter_finite_intersection.
    + apply isaprop_isfilter_notempty.
Qed.

(** *** Order on filters *)

Definition filter_le {X : UU} (F G : PreFilter X) :=
  ∏ A : hsubtype X, G A → F A.

Lemma istrans_filter_le {X : UU} :
  ∏ F G H : PreFilter X,
    filter_le F G → filter_le G H → filter_le F H.
Proof.
  intros F G H Hfg Hgh A Fa.
  apply Hfg, Hgh, Fa.
Qed.
Lemma isrefl_filter_le {X : UU} :
  ∏ F : PreFilter X, filter_le F F.
Proof.
  intros F A Fa.
  exact Fa.
Qed.
Lemma isantisymm_filter_le {X : UU} :
  ∏ F G : PreFilter X, filter_le F G → filter_le G F → F = G.
Proof.
  intros F G Hle Hge.
  simple refine (subtypePath_prop (B := λ _, make_hProp _ _) _).
  - apply isapropdirprod.
    + apply isaprop_isfilter_imply.
    + apply isaprop_isfilter_finite_intersection.
  - apply funextfun ; intros A.
    apply hPropUnivalence.
    + now apply Hge.
    + now apply Hle.
Qed.

Definition PartialOrder_filter_le (X : UU) : PartialOrder (make_hSet (PreFilter _) (isasetPreFilter X)).
Proof.
  simple refine (make_PartialOrder _ _).
  - intros F G.
    simple refine (make_hProp _ _).
    + apply (filter_le F G).
    + apply impred_isaprop ; intros A.
      apply isapropimpl.
      apply propproperty.
  - repeat split.
    + intros F G H ; simpl.
      apply istrans_filter_le.
    + intros A ; simpl.
      apply isrefl_filter_le.
    + intros F G ; simpl.
      apply isantisymm_filter_le.
Defined.

(** *** Image of a filter *)

Section filterim.

Context {X Y : UU}.
Context (f : X → Y) (F : hsubtype (hsubtype X)).
Context (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).

Definition filterim :=
  λ A : (hsubtype Y), F (λ x : X, A (f x)).

Lemma filterim_imply :
  isfilter_imply filterim.
Proof.
  intros A B H.
  apply Himp.
  intros x.
  apply (H (f x)).
Qed.
Lemma filterim_htrue :
  isfilter_htrue filterim.
Proof.
  apply Htrue.
Qed.
Lemma filterim_and :
  isfilter_and filterim.
Proof.
  intros A B.
  apply Hand.
Qed.
Lemma filterim_notempty :
  isfilter_notempty filterim.
Proof.
  intros A Fa.
  generalize (Hempty _ Fa).
  apply hinhfun.
  intros x.
  exists (f (pr1 x)).
  exact (pr2 x).
Qed.

End filterim.

Definition PreFilterIm {X Y : UU} (f : X → Y) (F : PreFilter X) : PreFilter Y.
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - exact (filterim f F).
  - apply filterim_imply, filter_imply.
  - apply filterim_htrue, filter_htrue.
  - apply filterim_and, filter_and.
Defined.

Definition FilterIm {X Y : UU} (f : X → Y) (F : Filter X) : Filter Y.
Proof.
  refine (tpair _ _ _).
  split.
  - apply (pr2 (PreFilterIm f F)).
  - apply filterim_notempty, filter_notempty.
Defined.

Lemma PreFilterIm_incr {X Y : UU} :
  ∏ (f : X → Y) (F G : PreFilter X),
    filter_le F G → filter_le (PreFilterIm f F) (PreFilterIm f G).
Proof.
  intros f F G Hle A ; simpl.
  apply Hle.
Qed.
Lemma FilterIm_incr {X Y : UU} :
  ∏ (f : X → Y) (F G : Filter X),
    filter_le F G → filter_le (FilterIm f F) (FilterIm f G).
Proof.
  intros f F G Hle A ; simpl.
  apply Hle.
Qed.

(** *** Limit: filter version *)

Definition filterlim {X Y : UU} (f : X → Y) (F : PreFilter X) (G : PreFilter Y) :=
  filter_le (PreFilterIm f F) G.

Lemma filterlim_comp {X Y Z : UU} :
  ∏ (f : X → Y) (g : Y → Z)
    (F : PreFilter X) (G : PreFilter Y) (H : PreFilter Z),
    filterlim f F G → filterlim g G H → filterlim (funcomp f g) F H.
Proof.
  intros f g F G H Hf Hg A Fa.
  specialize (Hg _ Fa).
  specialize (Hf _ Hg).
  apply Hf.
Qed.

Lemma filterlim_decr_1 {X Y : UU} :
  ∏ (f : X → Y) (F F' : PreFilter X) (G : PreFilter Y),
    filter_le F' F → filterlim f F G → filterlim f F' G.
Proof.
  intros f F F' G Hf Hle A Ha.
  specialize (Hle _ Ha).
  specialize (Hf _ Hle).
  apply Hf.
Qed.

Lemma filterlim_incr_2 {X Y : UU} :
  ∏ (f : X → Y) (F : PreFilter X) (G G' : PreFilter Y),
    filter_le G G' → filterlim f F G → filterlim f F G'.
Proof.
  intros f F G G' Hg Hle A Ha.
  specialize (Hg _ Ha).
  specialize (Hle _ Hg).
  exact Hle.
Qed.

(** ** Some usefull filters *)

(** *** Filter on a domain *)

Section filterdom.

Context {X : UU}.
Context (F : hsubtype (hsubtype X))
        (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).
Context (dom : hsubtype X)
        (Hdom : ∏ P, F P → ∃ x, dom x ∧ P x).

Definition filterdom : hsubtype (hsubtype X)
  := λ A : hsubtype X, F (λ x : X, make_hProp (dom x → A x) (isapropimpl _ _ (propproperty _))).

Lemma filterdom_imply :
  isfilter_imply filterdom.
Proof.
  intros A B Himpl.
  apply Himp.
  intros x Ax Hx.
  apply (Himpl x), Ax, Hx.
Qed.
Lemma filterdom_htrue :
  isfilter_htrue filterdom.
Proof.
  apply Himp with (2 := Htrue).
  intros x H _.
  exact H.
Qed.
Lemma filterdom_and :
  isfilter_and filterdom.
Proof.
  intros A B Ha Hb.
  generalize (Hand _ _ Ha Hb).
  apply Himp.
  intros x ABx Hx.
  split.
  - apply (pr1 ABx), Hx.
  - apply (pr2 ABx), Hx.
Qed.
Lemma filterdom_notempty :
  isfilter_notempty filterdom.
Proof.
  intros.
  intros A Fa.
  generalize (Hdom _ Fa).
  apply hinhfun.
  intros x.
  exists (pr1 x).
  apply (pr2 (pr2 x)), (pr1 (pr2 x)).
Qed.

End filterdom.

Definition PreFilterDom {X : UU} (F : PreFilter X) (dom : hsubtype X) : PreFilter X.
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - exact (filterdom F dom).
  - apply filterdom_imply, filter_imply.
  - apply filterdom_htrue.
    + apply filter_imply.
    + apply filter_htrue.
  - apply filterdom_and.
    + apply filter_imply.
    + apply filter_and.
Defined.

Definition FilterDom {X : UU} (F : Filter X) (dom : hsubtype X)
           (Hdom : ∏ P, F P → ∃ x, dom x ∧ P x) : Filter X.
Proof.
  refine (tpair _ _ _).
  split.
  - apply (pr2 (PreFilterDom F dom)).
  - apply filterdom_notempty.
    exact Hdom.
Defined.

(** *** Filter on a subtype *)

Section filtersubtype.

Context {X : UU}.
Context (F : hsubtype (hsubtype X))
        (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).
Context (dom : hsubtype X)
        (Hdom : ∏ P, F P → ∃ x, dom x ∧ P x).

Definition filtersubtype : hsubtype (hsubtype (∑ x : X, dom x)) :=
  λ A : hsubtype (∑ x : X, dom x),
        F (λ x : X, make_hProp (∏ Hx : dom x, A (x,, Hx)) (impred_isaprop _ (λ _, propproperty _))).

Lemma filtersubtype_imply :
  isfilter_imply filtersubtype.
Proof.
  intros A B Himpl.
  apply Himp.
  intros x Ax Hx.
  apply (Himpl (_ ,, _)), Ax.
Qed.
Lemma filtersubtype_htrue :
  isfilter_htrue filtersubtype.
Proof.
  apply Himp with (2 := Htrue).
  intros x H _.
  exact H.
Qed.
Lemma filtersubtype_and :
  isfilter_and filtersubtype.
Proof.
  intros A B Ha Hb.
  generalize (Hand _ _ Ha Hb).
  apply Himp.
  intros x ABx Hx.
  split.
  - apply (pr1 ABx).
  - apply (pr2 ABx).
Qed.
Lemma filtersubtype_notempty :
  isfilter_notempty filtersubtype.
Proof.
  intros A Fa.
  generalize (Hdom _ Fa).
  apply hinhfun.
  intros x.
  exists (pr1 x,,pr1 (pr2 x)).
  exact (pr2 (pr2 x) (pr1 (pr2 x))).
Qed.

End filtersubtype.

Definition PreFilterSubtype {X : UU} (F : PreFilter X) (dom : hsubtype X) : PreFilter (∑ x : X, dom x).
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - exact (filtersubtype F dom).
  - apply filtersubtype_imply, filter_imply.
  - apply filtersubtype_htrue.
    + apply filter_imply.
    + apply filter_htrue.
  - apply filtersubtype_and.
    + apply filter_imply.
    + apply filter_and.
Defined.

Definition FilterSubtype {X : UU} (F : Filter X) (dom : hsubtype X)
           (Hdom : ∏ P, F P → ∃ x, dom x ∧ P x) : Filter (∑ x : X, dom x).
Proof.
  refine (tpair _ _ _).
  split.
  - apply (pr2 (PreFilterSubtype F dom)).
  - apply filtersubtype_notempty.
    exact Hdom.
Defined.

(** *** Direct Product of filters *)

Section filterdirprod.

Context {X Y : UU}.
Context (Fx : hsubtype (hsubtype X))
        (Himp_x : isfilter_imply Fx)
        (Htrue_x : isfilter_htrue Fx)
        (Hand_x : isfilter_and Fx)
        (Hempty_x : isfilter_notempty Fx).
Context (Fy : hsubtype (hsubtype Y))
        (Himp_y : isfilter_imply Fy)
        (Htrue_y : isfilter_htrue Fy)
        (Hand_y : isfilter_and Fy)
        (Hempty_y : isfilter_notempty Fy).

Definition filterdirprod : hsubtype (hsubtype (X × Y)) :=
  λ A : hsubtype (X × Y),
        ∃ (Ax : hsubtype X) (Ay : hsubtype Y),
          Fx Ax × Fy Ay × (∏ (x : X) (y : Y), Ax x → Ay y → A (x,,y)).

Lemma filterdirprod_imply :
  isfilter_imply filterdirprod.
Proof.
  intros A B Himpl.
  apply hinhfun.
  intros C.
  generalize (pr1 C) (pr1 (pr2 C)) (pr1 (pr2 (pr2 C))) (pr1 (pr2 (pr2 (pr2 C)))) (pr2 (pr2 (pr2 (pr2 C)))) ;
  clear C ; intros Ax Ay Fax Fay Ha.
  exists Ax, Ay.
  repeat split.
  + exact Fax.
  + exact Fay.
  + intros x y Hx Hy.
    now apply (Himpl _), Ha.
Qed.
Lemma filterdirprod_htrue :
  isfilter_htrue filterdirprod.
Proof.
  apply hinhpr.
  exists (λ _:X, htrue), (λ _:Y, htrue).
  repeat split.
  + apply Htrue_x.
  + apply Htrue_y.
Qed.
Lemma filterdirprod_and :
  isfilter_and filterdirprod.
Proof.
  intros A B.
  apply hinhfun2.
  intros C D.
  generalize (pr1 C) (pr1 (pr2 C)) (pr1 (pr2 (pr2 C))) (pr1 (pr2 (pr2 (pr2 C)))) (pr2 (pr2 (pr2 (pr2 C)))) ;
  clear C ; intros Ax Ay Fax Fay Ha.
  generalize (pr1 D) (pr1 (pr2 D)) (pr1 (pr2 (pr2 D))) (pr1 (pr2 (pr2 (pr2 D)))) (pr2 (pr2 (pr2 (pr2 D)))) ;
  clear D ; intros Bx By Fbx Fby Hb.
  exists (λ x : X, Ax x ∧ Bx x), (λ y : Y, Ay y ∧ By y).
  repeat split.
  + now apply Hand_x.
  + now apply Hand_y.
  + apply Ha.
    * apply (pr1 X0).
    * apply (pr1 X1).
  + apply Hb.
    * apply (pr2 X0).
    * apply (pr2 X1).
Qed.
Lemma filterdirprod_notempty :
  isfilter_notempty filterdirprod.
Proof.
  intros A.
  apply hinhuniv.
  intros C.
  generalize (pr1 C) (pr1 (pr2 C)) (pr1 (pr2 (pr2 C))) (pr1 (pr2 (pr2 (pr2 C)))) (pr2 (pr2 (pr2 (pr2 C)))) ;
  clear C ; intros Ax Ay Fax Fay Ha.
  generalize (Hempty_x _ Fax) (Hempty_y _ Fay).
  apply hinhfun2.
  intros x y.
  exists (pr1 x,,pr1 y).
  apply Ha.
  - exact (pr2 x).
  - exact (pr2 y).
Qed.

End filterdirprod.

Definition PreFilterDirprod {X Y : UU} (Fx : PreFilter X) (Fy : PreFilter Y) : PreFilter (X × Y).
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - exact (filterdirprod Fx Fy).
  - apply filterdirprod_imply.
  - apply filterdirprod_htrue.
    + apply filter_htrue.
    + apply filter_htrue.
  - apply filterdirprod_and.
    + apply filter_and.
    + apply filter_and.
Defined.
Definition FilterDirprod {X Y : UU} (Fx : Filter X) (Fy : Filter Y) : Filter (X × Y).
Proof.
  refine (tpair _ _ _).
  split.
  - apply (pr2 (PreFilterDirprod Fx Fy)).
  - apply filterdirprod_notempty.
    + apply filter_notempty.
    + apply filter_notempty.
Defined.

Definition PreFilterPr1 {X Y : UU} (F : PreFilter (X × Y)) : PreFilter X :=
  (PreFilterIm pr1 F).
Definition FilterPr1 {X Y : UU} (F : Filter (X × Y)) : Filter X :=
  (FilterIm pr1 F).

Definition PreFilterPr2 {X Y : UU} (F : PreFilter (X × Y)) : PreFilter Y :=
  (PreFilterIm (@pr2 X (λ _ : X, Y)) F).
Definition FilterPr2 {X Y : UU} (F : Filter (X × Y)) : Filter Y :=
  (FilterIm (@pr2 X (λ _ : X, Y)) F).

Goal ∏ {X Y : UU} (F : PreFilter (X × Y)),
    filter_le F (PreFilterDirprod (PreFilterPr1 F) (PreFilterPr2 F)).
Proof.
  intros X Y F.
  intros A.
  apply hinhuniv.
  intros C ;
    generalize (pr1 C) (pr1 (pr2 C)) (pr1 (pr2 (pr2 C))) (pr1 (pr2 (pr2 (pr2 C)))) (pr2 (pr2 (pr2 (pr2 C)))) ;
    clear C ; intros Ax Ay Fax Fay Ha.
  simpl in *.
  generalize (filter_and _ _ _ Fax Fay).
  apply filter_imply.
  intros xy Fxy.
  apply Ha.
  - exact (pr1 Fxy).
  - exact (pr2 Fxy).
Qed.

Goal ∏ {X Y : UU} (F : PreFilter X) (G : PreFilter Y),
    filter_le (PreFilterPr1 (PreFilterDirprod F G)) F.
Proof.
  intros X Y F G.
  intros A Fa.
  apply hinhpr.
  exists A, (λ _, htrue).
  repeat split.
  - exact Fa.
  - now apply filter_htrue.
  - intros. assumption.
Qed.
Goal ∏ {X Y : UU} (F : PreFilter X) (G : PreFilter Y),
    filter_le (PreFilterPr2 (PreFilterDirprod F G)) G.
Proof.
  intros X Y F G.
  intros A Fa.
  apply hinhpr.
  exists (λ _, htrue), A.
  repeat split.
  - now apply filter_htrue.
  - exact Fa.
  - intros. assumption.
Qed.

(** ** Other filters *)

(** *** Filter on nat *)

Section filternat.

Definition filternat : hsubtype (hsubtype nat) :=
  λ P : hsubtype nat, ∃ N : nat, ∏ n : nat, N ≤ n → P n.

Lemma filternat_imply :
  isfilter_imply filternat.
Proof.
  intros P Q H.
  apply hinhfun.
  intros N.
  exists (pr1 N).
  intros n Hn.
  now apply (H _), (pr2 N).
Qed.
Lemma filternat_htrue :
  isfilter_htrue filternat.
Proof.
  apply hinhpr.
  now exists O.
Qed.
Lemma filternat_and :
  isfilter_and filternat.
Proof.
  intros A B.
  apply hinhfun2.
  intros Na Nb.
  exists (max (pr1 Na) (pr1 Nb)).
  intros n Hn.
  split.
  + apply (pr2 Na).
    eapply istransnatleh, Hn.
    now apply max_le_l.
  + apply (pr2 Nb).
    eapply istransnatleh, Hn.
    now apply max_le_r.
Qed.
Lemma filternat_notempty :
  isfilter_notempty filternat.
Proof.
  intros A.
  apply hinhfun.
  intros N.
  exists (pr1 N).
  apply (pr2 N (pr1 N)).
  now apply isreflnatleh.
Qed.

End filternat.

Definition FilterNat : Filter nat.
Proof.
  simple refine (make_Filter _ _ _ _ _).
  - apply filternat.
  - apply filternat_imply.
  - apply filternat_htrue.
  - apply filternat_and.
  - apply filternat_notempty.
Defined.

(** *** The upper filter *)

Section filtertop.

Context  {X : UU} (x0 : ∥ X ∥).

Definition filtertop : hsubtype (hsubtype X) :=
  λ A : hsubtype X, make_hProp (∏ x : X, A x) (impred_isaprop _ (λ _, propproperty _)).

Lemma filtertop_imply :
  isfilter_imply filtertop.
Proof.
  intros A B H Ha x.
  apply (H _).
  simple refine (Ha _).
Qed.
Lemma filtertop_htrue :
  isfilter_htrue filtertop.
Proof.
  intros x.
  apply tt.
Qed.
Lemma filtertop_and :
  isfilter_and filtertop.
Proof.
  intros A B Ha Hb x.
  split.
  + simple refine (Ha _).
  + simple refine (Hb _).
Qed.
Lemma filtertop_notempty :
  isfilter_notempty filtertop.
Proof.
  intros A Fa.
  revert x0.
  apply hinhfun.
  intros x0.
  exists x0.
  simple refine (Fa _).
Qed.

End filtertop.

Definition PreFilterTop {X : UU} : PreFilter X.
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - exact filtertop.
  - exact filtertop_imply.
  - exact filtertop_htrue.
  - exact filtertop_and.
Defined.

Definition FilterTop {X : UU} (x0 : ∥ X ∥) : Filter X.
Proof.
  refine (tpair _ _ _).
  split.
  - apply (pr2 PreFilterTop).
  - apply filtertop_notempty, x0.
Defined.

Lemma PreFilterTop_correct {X : UU} :
  ∏ (F : PreFilter X), filter_le F PreFilterTop.
Proof.
  intros F A Ha.
  apply filter_forall, Ha.
Qed.
Lemma FilterTop_correct {X : UU} :
  ∏ (x0 : ∥ X ∥) (F : Filter X), filter_le F (FilterTop x0).
Proof.
  intros x0 F A Ha.
  apply PreFilterTop_correct, Ha.
Qed.

(** *** Intersection of filters *)

Section filterintersection.

Context {X : UU}.
Context (is : (hsubtype (hsubtype X)) → UU).
Context (FF : hsubtype (∑ F : (hsubtype (hsubtype X)), is F))
        (Himp : ∏ F, FF F → isfilter_imply (pr1 F))
        (Htrue : ∏ F, FF F → isfilter_htrue (pr1 F))
        (Hand : ∏ F, FF F → isfilter_and (pr1 F))
        (Hempty : ∏ F, FF F → isfilter_notempty (pr1 F)).
Context (His : ∃ F, FF F).

Definition filterintersection : hsubtype (hsubtype X) :=
  λ A : hsubtype X, make_hProp (∏ F, FF F → (pr1 F) A)
                             (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).

Lemma filterintersection_imply :
  isfilter_imply filterintersection.
Proof.
  intros A B H Ha F Hf.
  apply (Himp F Hf A).
  - apply H.
  - simple refine (Ha _ _).
    exact Hf.
Qed.
Lemma filterintersection_htrue :
  isfilter_htrue filterintersection.
Proof.
  intros F Hf.
  now apply (Htrue F).
Qed.
Lemma filterintersection_and :
  isfilter_and filterintersection.
Proof.
  intros A B Ha Hb F Hf.
  apply (Hand F Hf).
  * now simple refine (Ha _ _).
  * now simple refine (Hb _ _).
Qed.
Lemma filterintersection_notempty :
  isfilter_notempty filterintersection.
Proof.
  intros A Fa.
  revert His.
  apply hinhuniv.
  intros F.
  apply (Hempty (pr1 F)).
  * exact (pr2 F).
  * simple refine (Fa _ _).
    exact (pr2 F).
Qed.

End filterintersection.

Definition PreFilterIntersection {X : UU} (FF : hsubtype (PreFilter X)) : PreFilter X.
Proof.
  intros.
  simple refine (make_PreFilter _ _ _ _).
  - apply (filterintersection _ FF).
  - apply filterintersection_imply.
    intros F _.
    apply filter_imply.
  - apply filterintersection_htrue.
    intros F _.
    apply filter_htrue.
  - apply filterintersection_and.
    intros F _.
    apply filter_and.
Defined.

Definition FilterIntersection {X : UU} (FF : hsubtype (Filter X))
           (Hff : ∃ F : Filter X, FF F) : Filter X.
Proof.
  simple refine (make_Filter _ _ _ _ _).
  - apply (filterintersection _ FF).
  - apply filterintersection_imply.
    intros F _.
    apply (filter_imply (pr1Filter _ F)).
  - apply filterintersection_htrue.
    intros F _.
    apply (filter_htrue (pr1Filter _ F)).
  - apply filterintersection_and.
    intros F _.
    apply (filter_and (pr1Filter _ F)).
  - apply filterintersection_notempty.
    + intros F _.
      apply (filter_notempty F).
    + exact Hff.
Defined.

Lemma PreFilterIntersection_glb {X : UU} (FF : hsubtype (PreFilter X)) :
  (∏ F : PreFilter X, FF F → filter_le F (PreFilterIntersection FF))
    × (∏ F : PreFilter X, (∏ G : PreFilter X, FF G → filter_le G F)
                          → filter_le (PreFilterIntersection FF) F).
Proof.
  split.
  - intros F Hf A Ha.
    now simple refine (Ha _ _).
  - intros F H A Fa G Hg.
    apply (H G Hg).
    apply Fa.
Qed.
Lemma FilterIntersection_glb {X : UU} (FF : hsubtype (Filter X)) Hff :
  (∏ F : Filter X, FF F → filter_le F (FilterIntersection FF Hff))
    × (∏ F : Filter X, (∏ G : Filter X, FF G → filter_le G F)
                       → filter_le (FilterIntersection FF Hff) F).
Proof.
  split.
  - intros F Hf A Ha.
    now simple refine (Ha _ _).
  - intros F H A Fa G Hg.
    apply (H G Hg).
    apply Fa.
Qed.

(** *** Filter generated by a set of subsets *)

Section filtergenerated.

Context {X : UU}.
Context (L : hsubtype (hsubtype X)).
Context (Hl : ∏ (L' : Sequence (hsubtype X)), (∏ m, L (L' m)) → ∃ x : X, ∏ m, L' m x).

Definition filtergenerated : hsubtype (hsubtype X) :=
  λ A : hsubtype X,
        ∃ (L' : Sequence (hsubtype X)), (∏ m, L (L' m)) × (finite_intersection L' ⊆ A).

Lemma filtergenerated_imply :
  isfilter_imply filtergenerated.
Proof.
  intros A B H.
  apply hinhfun ; intro Ha.
  exists (pr1 Ha), (pr1 (pr2 Ha)).
  intros x Hx.
  apply (H _).
  apply (pr2 (pr2 Ha) _), Hx.
Qed.
Lemma filtergenerated_htrue :
  isfilter_htrue filtergenerated.
Proof.
  apply hinhpr.
  exists nil.
  split.
  + intros m.
    induction (nopathsfalsetotrue (pr2 m)).
  + easy.
Qed.

Lemma filtergenerated_and :
  isfilter_and filtergenerated.
Proof.
  intros A B.
  apply hinhfun2.
  intros Ha Hb.
  exists (concatenate (pr1 Ha) (pr1 Hb)).
  split.
  + simpl ; intros m.
    unfold concatenate'.
    set (Hm := (weqfromcoprodofstn_invmap (length (pr1 Ha)) (length (pr1 Hb))) m).
    change ((weqfromcoprodofstn_invmap (length (pr1 Ha)) (length (pr1 Hb))) m) with Hm.
    induction Hm as [Hm | Hm].
    * rewrite coprod_rect_compute_1.
      apply (pr1 (pr2 Ha)).
    * rewrite coprod_rect_compute_2.
      apply (pr1 (pr2 Hb)).
  + intros x Hx.
    simpl in Hx.
    unfold concatenate' in Hx.
    split.
    * apply (pr2 (pr2 Ha) _).
      intros m.
      specialize (Hx (weqfromcoprodofstn_map _ _ (ii1 m))).
      rewrite (weqfromcoprodofstn_eq1 _ _), coprod_rect_compute_1 in Hx.
      exact Hx.
    * apply (pr2 (pr2 Hb) _).
      intros m.
      specialize (Hx (weqfromcoprodofstn_map _ _ (ii2 m))).
      rewrite (weqfromcoprodofstn_eq1 _ _), coprod_rect_compute_2 in Hx.
      exact Hx.
Qed.
Lemma filtergenerated_notempty :
  isfilter_notempty filtergenerated.
Proof.
  intros A.
  apply hinhuniv.
  intros L'.
  generalize (Hl _ (pr1 (pr2 L'))).
  apply hinhfun.
  intros x.
  exists (pr1 x).
  apply (pr2 (pr2 L') _).
  exact (pr2 x).
Qed.

End filtergenerated.

Definition PreFilterGenerated {X : UU} (L : hsubtype (hsubtype X)) : PreFilter X.
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - apply (filtergenerated L).
  - apply filtergenerated_imply.
  - apply filtergenerated_htrue.
  - apply filtergenerated_and.
Defined.

Definition FilterGenerated {X : UU} (L : hsubtype (hsubtype X))
           (Hl : ∏ L' : Sequence (hsubtype X),
  (∏ m : stn (length L'), L (L' m)) → ∃ x : X, finite_intersection L' x) : Filter X.
Proof.
  exists (PreFilterGenerated L).
  split.
  - apply (pr2 (PreFilterGenerated L)).
  - apply filtergenerated_notempty.
    exact Hl.
Defined.

Lemma PreFilterGenerated_correct {X : UU} :
   ∏ (L : hsubtype (hsubtype X)),
   (∏ A : hsubtype X, L A → (PreFilterGenerated L) A)
   × (∏ F : PreFilter X,
      (∏ A : hsubtype X, L A → F A) → filter_le F (PreFilterGenerated L)).
Proof.
  intros L.
  split.
  - intros A La.
    apply hinhpr.
    exists (singletonSequence A).
    split.
    + intros. assumption.
    + intros x Hx.
      apply (Hx (O,,paths_refl _)).
  - intros F Hf A.
    apply hinhuniv.
    intros Ha.
    refine (filter_imply _ _ _ _ _).
    + apply (pr2 (pr2 Ha)).
    + apply filter_finite_intersection.
      intros m.
      apply Hf.
      apply (pr1 (pr2 Ha)).
Qed.
Lemma FilterGenerated_correct {X : UU} :
   ∏ (L : hsubtype (hsubtype X))
   (Hl : ∏ L' : Sequence (hsubtype X),
         (∏ m, L (L' m)) →
         (∃ x : X, finite_intersection L' x)),
   (∏ A : hsubtype X, L A → (FilterGenerated L Hl) A)
   × (∏ F : Filter X,
      (∏ A : hsubtype X, L A → F A) → filter_le F (FilterGenerated L Hl)).
Proof.
  intros L Hl.
  split.
  - intros A La.
    apply hinhpr.
    exists (singletonSequence A).
    split.
    + intros; assumption.
    + intros x Hx.
      apply (Hx (O,,paths_refl _)).
  - intros F Hf A.
    apply hinhuniv.
    intros Ha.
    refine (filter_imply _ _ _ _ _).
    + apply (pr2 (pr2 Ha)).
    + apply filter_finite_intersection.
      intros m.
      apply Hf.
      apply (pr1 (pr2 Ha)).
Qed.

Lemma FilterGenerated_inv {X : UU} :
   ∏ (L : hsubtype (hsubtype X)) (F : Filter X),
   (∏ A : hsubtype X, L A → F A) →
   ∏ (L' : Sequence (hsubtype X)),
   (∏ m, L (L' m)) →
   (∃ x : X, finite_intersection L' x).
Proof.
  intros L F Hf L' Hl'.
  apply (filter_notempty F).
  apply filter_finite_intersection.
  intros m.
  apply Hf, Hl'.
Qed.

Lemma ex_filter_le {X : UU} :
  ∏ (F : Filter X) (A : hsubtype X),
    (∑ G : Filter X, filter_le G F × G A)
    <-> (∏ B : hsubtype X, F B → (∃ x : X, A x ∧ B x)).
Proof.
  intros F A.
  split.
  - intros G B Fb.
    apply (filter_notempty (pr1 G)).
    apply filter_and.
    + apply (pr2 (pr2 G)).
    + now apply (pr1 (pr2 G)).
  - intros H.
    simple refine (tpair _ _ _).
    + simple refine (FilterGenerated _ _).
      * intros B.
        apply (F B ∨ B = A).
      * intros L Hl.
        assert (B : ∃ B : hsubtype X, F B × ((A ∩ B) ⊆ A ∩ finite_intersection L)).
        { revert L Hl.
          apply (Sequence_rect (P := λ L : Sequence (hsubtype X),
                                    (∏ m : stn (length L), (λ B : hsubtype X, F B ∨ B = A) (L m)) →
                                    ∃ B : hsubtype X,
                                      F B × (A ∩ B ⊆ A ∩ finite_intersection L))).
        - intros Hl.
          apply hinhpr.
          exists (λ _, htrue).
          split.
          + exact (filter_htrue F).
          + intros x Hx.
            refine (transportf (λ y, _ ∧ y x) (!finite_intersection_htrue) _).
            assumption.
        - intros L B IHl Hl.
          simple refine (hinhuniv _ (IHl _)).
          + intros C.
            refine (transportf (λ y, ∃ B, F B × (∏ x, _ → _ ∧ y x)) (!finite_intersection_append _ _) _).
            generalize (Hl lastelement) ; simpl.
            rewrite append_vec_compute_2.
            apply hinhfun.
            apply sumofmaps ; [intros Fl | intros ->].
            * refine (tpair _ _ _).
              split.
              ** apply (filter_and F).
                 *** apply (pr1 (pr2 C)).
                 *** apply Fl.
              ** intros x H0 ; repeat split.
                 *** exact (pr1 H0).
                 *** exact (pr2 (pr2 H0)).
                 *** simple refine (pr2 (pr2 (pr2 C) x _)).
                     split.
                     **** exact (pr1 H0).
                     **** exact (pr1 (pr2 H0)).
            * exists (pr1 C) ; split.
              ** exact (pr1 (pr2 C)).
              ** intros x H0 ; repeat split.
                 *** exact (pr1 H0).
                 *** exact (pr1 H0).
                 *** simple refine (pr2 (pr2 (pr2 C) x _)).
                     exact H0.
          + intros.
            generalize (Hl (dni_lastelement m)) ; simpl.
            rewrite <- replace_dni_last.
            now rewrite append_vec_compute_1. }
      revert B.
      apply hinhuniv.
      intros B.
      generalize (H (pr1 B) (pr1 (pr2 B))).
      apply hinhfun.
      intros x.
      exists (pr1 x).
      simple refine (pr2 (pr2 (pr2 B) (pr1 x) _)).
      exact (pr2 x).
    + split.
      * intros B Fb.
        apply hinhpr.
        exists (singletonSequence B).
        split.
        ** intros m.
           apply hinhpr.
           now left.
        ** intros x Hx.
           apply (Hx (O ,, paths_refl _)).
      * apply hinhpr.
        exists (singletonSequence A).
        split.
        ** intros m.
           apply hinhpr.
           now right.
        ** intros x Hx.
           apply (Hx (O ,, paths_refl _)).
Qed.

(** *** Filter defined by a base *)

Section base.

Context {X : UU}.
Context (base : hsubtype (hsubtype X)).

Definition isbase_and :=
  ∏ A B : hsubtype X, base A → base B → ∃ C : hsubtype X, base C × (C ⊆ A ∩ B).
Definition isbase_notempty :=
  ∃ A : hsubtype X, base A.
Definition isbase_notfalse :=
  ∏ A, base A → ∃ x, A x.

Definition isBaseOfPreFilter :=
  isbase_and × isbase_notempty.
Definition isBaseOfFilter :=
  isbase_and × isbase_notempty × isbase_notfalse.

End base.

Definition BaseOfPreFilter (X : UU) :=
  ∑ (base : hsubtype (hsubtype X)), isBaseOfPreFilter base.
Definition pr1BaseOfPreFilter {X : UU} : BaseOfPreFilter X → (hsubtype X) → hProp := pr1.
Coercion pr1BaseOfPreFilter : BaseOfPreFilter >-> Funclass.

Definition BaseOfFilter (X : UU) :=
  ∑ (base : hsubtype (hsubtype X)), isBaseOfFilter base.
Definition pr1BaseOfFilter {X : UU} : BaseOfFilter X → BaseOfPreFilter X.
Proof.
  intros base.
  exists (pr1 base).
  split.
  - apply (pr1 (pr2 base)).
  - apply (pr1 (pr2 (pr2 base))).
Defined.
Coercion pr1BaseOfFilter : BaseOfFilter >-> BaseOfPreFilter.

  Lemma BaseOfPreFilter_and {X : UU} (base : BaseOfPreFilter X) :
  ∏ A B : hsubtype X, base A → base B → ∃ C : hsubtype X, base C × (C ⊆ A ∩ B).
Proof.
  apply (pr1 (pr2 base)).
Qed.
Lemma BaseOfPreFilter_notempty {X : UU} (base : BaseOfPreFilter X) :
  ∃ A : hsubtype X, base A.
Proof.
  apply (pr2 (pr2 base)).
Qed.

Lemma BaseOfFilter_and {X : UU} (base : BaseOfFilter X) :
  ∏ A B : hsubtype X, base A → base B → ∃ C : hsubtype X, base C × (C ⊆ A ∩ B).
Proof.
  apply (pr1 (pr2 base)).
Qed.
Lemma BaseOfFilter_notempty {X : UU} (base : BaseOfFilter X) :
  ∃ A : hsubtype X, base A.
Proof.
  apply (pr1 (pr2 (pr2 base))).
Qed.
Lemma BaseOfFilter_notfalse {X : UU} (base : BaseOfFilter X) :
  ∏ A, base A → ∃ x, A x.
Proof.
  apply (pr2 (pr2 (pr2 base))).
Qed.

Section filterbase.

Context {X : UU}.
Context (base : hsubtype (hsubtype X))
        (Hand : isbase_and base)
        (Hempty : isbase_notempty base)
        (Hfalse : isbase_notfalse base).

Definition filterbase : hsubtype (hsubtype X) :=
  λ A : hsubtype X, (∃ B : hsubtype X, base B × B ⊆ A).

Lemma filterbase_imply :
  isfilter_imply filterbase.
Proof.
  intros A B H.
  apply hinhfun.
  intros A'.
  exists (pr1 A').
  split.
  - apply (pr1 (pr2 A')).
  - intros x Hx.
    apply (H _).
    now apply (pr2 (pr2 A') _).
Qed.

Lemma filterbase_htrue :
  isfilter_htrue filterbase.
Proof.
  revert Hempty.
  apply hinhfun.
  intros A.
  exists (pr1 A).
  split.
  - apply (pr2 A).
  - intros x Hx. exact tt.
Qed.
Lemma filterbase_and :
  isfilter_and filterbase.
Proof.
  intros A B.
  apply hinhuniv2.
  intros A' B'.
  refine (hinhfun _ _).
  2: apply Hand.
  2: (apply (pr1 (pr2 A'))).
  2: (apply (pr1 (pr2 B'))).
  intros C'.
  exists (pr1 C').
  split.
  - apply (pr1 (pr2 C')).
  - intros x Cx ; split.
    + apply (pr2 (pr2 A') _).
      now refine (pr1 (pr2 (pr2 C') _ _)).
    + apply (pr2 (pr2 B') _).
      now refine (pr2 (pr2 (pr2 C') _ _)).
Qed.
Lemma filterbase_notempty :
  isfilter_notempty filterbase.
Proof.
  intros A.
  apply hinhuniv.
  intros B.
  generalize (Hfalse _ (pr1 (pr2 B))).
  apply hinhfun.
  intros x.
  exists (pr1 x).
  apply (pr2 (pr2 B) _), (pr2 x).
Qed.

Lemma base_finite_intersection :
  ∏ L : Sequence (hsubtype X),
    (∏ n, base (L n)) → ∃ A, base A × (A ⊆ finite_intersection L).
Proof.
  intros L Hbase.
  apply (pr2 (finite_intersection_hProp (λ B, ∃ A : hsubtype X, base A × (A ⊆ B)))).
  - split.
    + revert Hempty.
      apply hinhfun.
      intros A.
      now exists (pr1 A), (pr2 A).
    + intros A B.
      apply hinhuniv2.
      intros A' B'.
      generalize (Hand _ _ (pr1 (pr2 A')) (pr1 (pr2 B'))).
      apply hinhfun.
      intros C.
      exists (pr1 C).
      split.
      * exact (pr1 (pr2 C)).
      * intros x Cx.
        split.
        ** apply (pr2 (pr2 A') _), (pr1 (pr2 (pr2 C) _ Cx)).
        ** apply (pr2 (pr2 B') _), (pr2 (pr2 (pr2 C) _ Cx)).
  - intros n.
    apply hinhpr.
    exists (L n).
    split.
    + now apply Hbase.
    + intros x Hx; assumption.
Qed.

Lemma filterbase_genetated :
  filterbase = filtergenerated base.
Proof.
  apply funextfun ; intros P.
  apply hPropUnivalence.
  - apply hinhfun.
    intros A.
    exists (singletonSequence (pr1 A)).
    split.
    + intros m ; simpl.
      exact (pr1 (pr2 A)).
    + intros x Ax.
      apply (pr2 (pr2 A) _).
      simple refine (Ax _).
      now exists 0%nat.
  - apply hinhuniv.
    intros L.
    generalize (base_finite_intersection (pr1 L) (pr1 (pr2 L))).
    apply hinhfun.
    intros A.
    exists (pr1 A) ; split.
    + exact (pr1 (pr2 A)).
    + intros x Ax.
      now apply (pr2 (pr2 L) _), (pr2 (pr2 A) _).
Qed.

Lemma filterbase_generated_hypothesis :
  ∏ L' : Sequence (hsubtype X),
    (∏ m : stn (length L'), base (L' m))
    → ∃ x : X, finite_intersection L' x.
Proof.
  intros L Hbase.
  generalize (base_finite_intersection L Hbase).
  apply hinhuniv.
  intros A.
  generalize (Hfalse _ (pr1 (pr2 A))).
  apply hinhfun.
  intros x.
  exists (pr1 x).
  apply (pr2 (pr2 A) _).
  exact (pr2 x).
Qed.

End filterbase.

Definition PreFilterBase {X : UU} (base : BaseOfPreFilter X) : PreFilter X.
Proof.
  simple refine (make_PreFilter _ _ _ _).
  - apply (filterbase base).
  - apply filterbase_imply.
  - apply filterbase_htrue, BaseOfPreFilter_notempty.
  - apply filterbase_and.
    intros A B.
    now apply BaseOfPreFilter_and.
Defined.
Definition FilterBase {X : UU} (base : BaseOfFilter X) : Filter X.
Proof.
  intros.
  exists (pr1 (PreFilterBase base)).
  split.
  - simple refine (pr2 (PreFilterBase base)).
  - apply filterbase_notempty.
    intros A Ha.
    simple refine (BaseOfFilter_notfalse _ _ _).
    + apply base.
    + apply Ha.
Defined.

Lemma PreFilterBase_Generated {X : UU} (base : BaseOfPreFilter X) :
  PreFilterBase base = PreFilterGenerated base.
Proof.
  simple refine (subtypePath_prop (B := λ _, make_hProp _ _) _).
  - apply isapropdirprod.
    + apply isaprop_isfilter_imply.
    + apply isaprop_isfilter_finite_intersection.
  - simpl.
    apply filterbase_genetated.
    + intros A B.
      apply (BaseOfPreFilter_and base).
    + apply (BaseOfPreFilter_notempty base).
Qed.

Lemma FilterBase_Generated {X : UU} (base : BaseOfFilter X) Hbase :
  FilterBase base = FilterGenerated base Hbase.
Proof.
  simple refine (subtypePath_prop (B := λ _, make_hProp _ _) _).
  - apply isapropdirprod.
    + apply isapropdirprod.
      * apply isaprop_isfilter_imply.
      * apply isaprop_isfilter_finite_intersection.
    + apply isaprop_isfilter_notempty.
  - simpl.
    apply filterbase_genetated.
    + intros A B.
      apply (BaseOfFilter_and base).
    + apply (BaseOfFilter_notempty base).
Qed.

Lemma FilterBase_Generated_hypothesis {X : UU} (base : BaseOfFilter X) :
  ∏ L' : Sequence (hsubtype X),
    (∏ m : stn (length L'), base (L' m))
    → ∃ x : X, finite_intersection L' x.
Proof.
  apply filterbase_generated_hypothesis.
  - intros A B.
    apply (BaseOfFilter_and base).
  - apply (BaseOfFilter_notempty base).
  - intros A Ha.
    now apply (BaseOfFilter_notfalse base).
Qed.

Lemma filterbase_le {X : UU} (base base' : hsubtype (hsubtype X)) :
  (∏ P : hsubtype X, base P → ∃ Q : hsubtype X, base' Q × (Q ⊆ P))
  <-> (filterbase base ⊆ filterbase base').
Proof.
  split.
  - intros Hbase P.
    cbn -[filterbase].
    apply hinhuniv.
    intros A.
    generalize (Hbase _ (pr1 (pr2 A))).
    apply hinhfun.
    intros B.
    exists (pr1 B).
    split.
    + apply (pr1 (pr2 B)).
    + intros x Bx.
      apply (pr2 (pr2 A) _), (pr2 (pr2 B) _), Bx.
  - intros Hbase P Hp.
    apply (Hbase _).
    apply hinhpr.
    exists P.
    split.
    + exact Hp.
    + intro x.
      exact (idfun _).
Qed.

Lemma PreFilterBase_le {X : UU} (base base' : BaseOfPreFilter X) :
  (∏ P : hsubtype X, base P → ∃ Q : hsubtype X, base' Q × (Q ⊆ P))
  <-> filter_le (PreFilterBase base') (PreFilterBase base).
Proof.
  split.
  - intros Hbase P.
    exact (pr1 (filterbase_le base base') Hbase _).
  - apply (pr2 (filterbase_le base base')).
Qed.
Lemma FilterBase_le {X : UU} (base base' : BaseOfFilter X) :
  (∏ P : hsubtype X, base P → ∃ Q : hsubtype X, base' Q × (Q ⊆ P))
  <-> filter_le (FilterBase base') (FilterBase base).
Proof.
  split.
  - intros Hbase P.
    apply (pr1 (filterbase_le base base') Hbase _).
  - apply (pr2 (filterbase_le base base')).
Qed.
