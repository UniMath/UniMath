(** * Results about Filters *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Analysis.Complements.

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** ** Definition of a Filter *)

Section Filter_def.

Context {X : UU}.
Context (F : (X -> hProp) -> hProp).

Definition isfilter_imply :=
  ∀ A B : X -> hProp, (∀ x : X, A x -> B x) -> F A -> F B.
Lemma isaprop_isfilter_imply : isaprop isfilter_imply.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropimpl.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition isfilter_finite_intersection :=
  ∀ (L : Sequence (X -> hProp)), (∀ n, F (L n)) -> F (finite_intersection L).
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
  ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x).
Lemma isaprop_isfilter_and : isaprop isfilter_and.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropimpl.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition isfilter_notempty :=
  ¬ F (λ _ : X, hfalse).
Lemma isaprop_isfilter_notempty :
  isaprop isfilter_notempty.
Proof.
  apply isapropneg.
Qed.

Lemma isfilter_finite_intersection_htrue :
  isfilter_finite_intersection -> isfilter_htrue.
Proof.
  intros Hand.
  unfold isfilter_htrue.
  rewrite <- finite_intersection_htrue.
  apply Hand.
  intros (m,Hm).
  apply fromempty.
  revert Hm.
  now apply negnatlthn0.
Qed.

Lemma isfilter_finite_intersection_and :
  isfilter_finite_intersection -> isfilter_and.
Proof.
  intros Hand A B Fa Fb.
  rewrite <- finite_intersection_and.
  apply Hand.
  intros (m,Hm) ; simpl.
  destruct m.
  exact Fa.
  exact Fb.
Qed.

Lemma isfilter_finite_intersection_carac :
  isfilter_htrue -> isfilter_and
  -> isfilter_finite_intersection.
Proof.
  intros Htrue Hand L.
  apply (pr2 (finite_intersection_hProp F)).
  split.
  - exact Htrue.
  - exact Hand.
Qed.

End Filter_def.

Definition isPreFilter {X : UU} (F : (X -> hProp) -> hProp) :=
  isfilter_imply F × isfilter_finite_intersection F.
Definition PreFilter (X : UU) :=
  Σ (F : (X -> hProp) -> hProp), isPreFilter F.
Definition mkPreFilter {X : UU} (F : (X -> hProp) -> hProp)
           (Himpl : isfilter_imply F)
           (Htrue : isfilter_htrue F)
           (Hand : isfilter_and F) : PreFilter X :=
  F,, Himpl,, isfilter_finite_intersection_carac F Htrue Hand.

Definition pr1PreFilter (X : UU) (F : PreFilter X) : (X -> hProp) -> hProp := pr1 F.
Coercion pr1PreFilter : PreFilter >-> Funclass.

Definition isFilter {X : UU} (F : (X -> hProp) -> hProp) :=
  isPreFilter F × isfilter_notempty F.
Definition Filter (X : UU) := Σ F : (X -> hProp) -> hProp, isFilter F.
Definition pr1Filter (X : UU) (F : Filter X) : PreFilter X :=
  pr1 F,, pr1 (pr2 F).
Coercion pr1Filter : Filter >-> PreFilter.
Definition mkFilter {X : UU} (F : (X -> hProp) -> hProp) (Himp : isfilter_imply F) (Htrue : isfilter_htrue F) (Hand : isfilter_and F) (Hempty : isfilter_notempty F) : Filter X :=
  F ,, (Himp ,, (isfilter_finite_intersection_carac F Htrue Hand)) ,, Hempty.

Lemma emptynofilter :
  ∀ F : (empty -> hProp) -> hProp,
    ¬ isFilter F.
Proof.
  intros F ((Himp,Hand),Hempty).
  apply Hempty.
  apply isfilter_finite_intersection_htrue in Hand.
  assert ((λ _ : ∅, hfalse) = (λ _ : ∅, htrue)).
  apply funextfun, fromempty.
  rewrite X.
  exact Hand.
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
  ∀ A : X -> hProp, (∀ x : X, A x) -> F A.
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
  ∀ A : hProp, F (λ _ : X, A) -> ¬ (¬ A).
Proof.
  intros A Fa Ha.
  apply filter_notempty.
  revert Fa.
  apply filter_imply.
  intros _.
  exact Ha.
Qed.

End Filter_pty.

Lemma isasetPreFilter (X : UU) : isaset (PreFilter X).
Proof.
  intros X.
  simple refine (isaset_total2_subset (hSetpair _ _) (λ _, hProppair _ _)).
  apply impred_isaset ; intros _.
  apply isasethProp.
  apply isapropdirprod.
  apply isaprop_isfilter_imply.
  apply isaprop_isfilter_finite_intersection.
Qed.

Lemma isasetFilter (X : UU) : isaset (Filter X).
Proof.
  intros X.
  simple refine (isaset_total2_subset (hSetpair _ _) (λ _, hProppair _ _)).
  apply impred_isaset ; intros _.
  apply isasethProp.
  apply isapropdirprod.
  apply isapropdirprod.
  apply isaprop_isfilter_imply.
  apply isaprop_isfilter_finite_intersection.
  apply isaprop_isfilter_notempty.
Qed.

(** *** Order on filters *)

Definition filter_le {X : UU} (F G : PreFilter X) :=
  ∀ A : X -> hProp, G A -> F A.

Lemma istrans_filter_le {X : UU} :
  ∀ F G H : PreFilter X,
    filter_le F G -> filter_le G H -> filter_le F H.
Proof.
  intros X.
  intros F G H Hfg Hgh A Fa.
  apply Hfg, Hgh, Fa.
Qed.
Lemma isrefl_filter_le {X : UU} :
  ∀ F : PreFilter X, filter_le F F.
Proof.
  intros X F A Fa.
  exact Fa.
Qed.
Lemma isantisymm_filter_le {X : UU} :
  ∀ F G : PreFilter X, filter_le F G -> filter_le G F -> F = G.
Proof.
  intros X F G Hle Hge.
  simple refine (subtypeEquality_prop (B := λ _, hProppair _ _) _).
  apply isapropdirprod.
  apply isaprop_isfilter_imply.
  apply isaprop_isfilter_finite_intersection.
  apply funextfun ; intros A.
  apply uahp.
  now apply Hge.
  now apply Hle.
Qed.

Definition PartialOrder_filter_le (X : UU) : PartialOrder (hSetpair (PreFilter _) (isasetPreFilter X)).
Proof.
  intros X.
  simple refine (PartialOrderpair _ _).
  - intros F G.
    simple refine (hProppair _ _).
    apply (filter_le F G).
    apply impred_isaprop ; intros A.
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

Section filtermap.

Context {X Y : UU}.
Context (f : X -> Y) (F : (X -> hProp) -> hProp).
Context (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).

Definition filtermap :=
  λ A : (Y -> hProp), F (λ x : X, A (f x)).

Lemma filtermap_imply :
  isfilter_imply filtermap.
Proof.
  intros A B H.
  apply Himp.
  intros x.
  apply H.
Qed.
Lemma filtermap_htrue :
  isfilter_htrue filtermap.
Proof.
  apply Htrue.
Qed.
Lemma filtermap_and :
  isfilter_and filtermap.
Proof.
  intros A B.
  apply Hand.
Qed.
Lemma filtermap_notempty :
  isfilter_notempty filtermap.
Proof.
  apply Hempty.
Qed.

End filtermap.

Definition PreFilterMap {X Y : UU} (f : X -> Y) (F : PreFilter X) : PreFilter Y.
Proof.
  intros.
  simple refine (mkPreFilter _ _ _ _).
  exact (filtermap f F).
  apply filtermap_imply, filter_imply.
  apply filtermap_htrue, filter_htrue.
  apply filtermap_and, filter_and.
Defined.

Definition FilterMap {X Y : UU} (f : X -> Y) (F : Filter X) : Filter Y.
Proof.
  intros X Y f F.
  refine (tpair _ _ _).
  split.
  apply (pr2 (PreFilterMap f F)).
  apply filtermap_notempty, filter_notempty.
Defined.

Lemma PreFilterMap_incr {X Y : UU} :
  ∀ (f : X -> Y) (F G : PreFilter X),
    filter_le F G -> filter_le (PreFilterMap f F) (PreFilterMap f G).
Proof.
  intros X Y.
  intros f F G Hle A ; simpl.
  apply Hle.
Qed.
Lemma FilterMap_incr {X Y : UU} :
  ∀ (f : X -> Y) (F G : Filter X),
    filter_le F G -> filter_le (FilterMap f F) (FilterMap f G).
Proof.
  intros X Y.
  intros f F G Hle A ; simpl.
  apply Hle.
Qed.

(** *** Limit: filter version *)

Definition filterlim {X Y : UU} (f : X -> Y) (F : PreFilter X) (G : PreFilter Y) :=
  filter_le (PreFilterMap f F) G.

Lemma filterlim_comp {X Y Z : UU} :
  ∀ (f : X -> Y) (g : Y -> Z)
    (F : PreFilter X) (G : PreFilter Y) (H : PreFilter Z),
    filterlim f F G -> filterlim g G H -> filterlim (λ x : X, g (f x)) F H.
Proof.
  intros X Y Z.
  intros f g F G H Hf Hg A Fa.
  specialize (Hg _ Fa).
  specialize (Hf _ Hg).
  apply Hf.
Qed.

Lemma filterlim_decr_1 {X Y : UU} :
  ∀ (f : X -> Y) (F F' : PreFilter X) (G : PreFilter Y),
    filter_le F' F -> filterlim f F G -> filterlim f F' G.
Proof.
  intros X Y.
  intros f F F' G Hf Hle A Ha.
  specialize (Hle _ Ha).
  specialize (Hf _ Hle).
  apply Hf.
Qed.

Lemma filterlim_incr_2 {X Y : UU} :
  ∀ (f : X -> Y) (F : PreFilter X) (G G' : PreFilter Y),
    filter_le G G' -> filterlim f F G -> filterlim f F G'.
Proof.
  intros X Y.
  intros f F G G' Hg Hle A Ha.
  specialize (Hg _ Ha).
  specialize (Hle _ Hg).
  exact Hle.
Qed.

(** ** Some usefull filters *)

(** *** Filter on a domain *)

Section filterdom.

Context {X : UU}.
Context (F : (X -> hProp) -> hProp)
        (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).
Context (dom : X -> hProp)
        (Hdom : ∀ P, F P -> ¬ ¬ ∃ x, dom x ∧ P x).

Definition filterdom : (X -> hProp) -> hProp
  := λ A : X → hProp, F (λ x : X, hProppair (dom x → A x) (isapropimpl _ _ (propproperty _))).

Lemma filterdom_imply :
  isfilter_imply filterdom.
Proof.
  intros A B Himpl.
  apply Himp.
  intros x Ax Hx.
  apply Himpl, Ax, Hx.
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
  intros x (Ax,Bx) Hx.
  split.
  - apply Ax, Hx.
  - apply Bx, Hx.
Qed.
Lemma filterdom_notempty :
  isfilter_notempty filterdom.
Proof.
  intro Hf.
  apply Hdom in Hf.
  apply Hf.
  unfold neg.
  apply hinhuniv'.
  exact isapropempty.
  intros (x,(Hx,Hx')).
  now apply Hx'.
Qed.

End filterdom.

Definition PreFilterDom {X : UU} (F : PreFilter X) (dom : X -> hProp) : PreFilter X.
Proof.
  intros X F dom.
  simple refine (mkPreFilter _ _ _ _).
  - exact (filterdom F dom).
  - apply filterdom_imply, filter_imply.
  - apply filterdom_htrue.
    apply filter_imply.
    apply filter_htrue.
  - apply filterdom_and.
    apply filter_imply.
    apply filter_and.
Defined.

Definition FilterDom {X : UU} (F : Filter X) (dom : X -> hProp) (Hdom : ∀ P, F P -> ¬ ¬ ∃ x, dom x ∧ P x) : Filter X.
Proof.
  intros X F dom Hdom.
  refine (tpair _ _ _).
  split.
  apply (pr2 (PreFilterDom F dom)).
  apply filterdom_notempty.
  exact Hdom.
Defined.

(** *** Filter on a subtype *)

Section filtersubtype.

Context {X : UU}.
Context (F : (X -> hProp) -> hProp)
        (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).
Context (dom : X -> hProp)
        (Hdom : ∀ P, F P -> ¬ ¬ ∃ x, dom x ∧ P x).

Definition filtersubtype : ((Σ x : X, dom x) -> hProp) -> hProp :=
  λ A : (Σ x : X, dom x) → hProp,
        F (λ x : X, hProppair (∀ Hx : dom x, A (x,, Hx)) (impred_isaprop _ (λ _, propproperty _))).

Lemma filtersubtype_imply :
  isfilter_imply filtersubtype.
Proof.
  intros A B Himpl.
  apply Himp.
  intros x Ax Hx.
  apply Himpl, Ax.
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
  intros x (Ax,Bx) Hx.
  split.
  - apply Ax.
  - apply Bx.
Qed.
Lemma filtersubtype_notempty :
  isfilter_notempty filtersubtype.
Proof.
  intro Hf.
  apply Hdom in Hf.
  apply Hf.
  unfold neg.
  apply hinhuniv'.
  exact isapropempty.
  intros (x,(Hx,Hx')).
  now apply Hx'.
Qed.

End filtersubtype.

Definition PreFilterSubtype {X : UU} (F : PreFilter X) (dom : X -> hProp) : PreFilter (Σ x : X, dom x).
Proof.
  intros X F dom.
  simple refine (mkPreFilter _ _ _ _).
  - exact (filtersubtype F dom).
  - apply filtersubtype_imply, filter_imply.
  - apply filtersubtype_htrue.
    apply filter_imply.
    apply filter_htrue.
  - apply filtersubtype_and.
    apply filter_imply.
    apply filter_and.
Defined.

Definition FilterSubtype {X : UU} (F : Filter X) (dom : X -> hProp) (Hdom : ∀ P, F P -> ¬ ¬ ∃ x, dom x ∧ P x) : Filter (Σ x : X, dom x).
Proof.
  intros X F dom Hdom.
  refine (tpair _ _ _).
  split.
  apply (pr2 (PreFilterSubtype F dom)).
  apply filtersubtype_notempty.
  exact Hdom.
Defined.

(** *** Direct Product of filters *)

Section filterdirprod.

Context {X Y : UU}.
Context (Fx : (X -> hProp) -> hProp)
        (Himp_x : isfilter_imply Fx)
        (Htrue_x : isfilter_htrue Fx)
        (Hand_x : isfilter_and Fx)
        (Hempty_x : isfilter_notempty Fx).
Context (Fy : (Y -> hProp) -> hProp)
        (Himp_y : isfilter_imply Fy)
        (Htrue_y : isfilter_htrue Fy)
        (Hand_y : isfilter_and Fy)
        (Hempty_y : isfilter_notempty Fy).

Definition filterdirprod : (X × Y -> hProp) -> hProp :=
  λ A : (X × Y) -> hProp,
        ∃ (Ax : X -> hProp) (Ay : Y -> hProp), Fx Ax × Fy Ay × (∀ (x : X) (y : Y), Ax x -> Ay y -> A (x,,y)).

Lemma filterdirprod_imply :
  isfilter_imply filterdirprod.
Proof.
  intros A B Himpl.
  apply hinhfun.
  intros (Ax,(Ay,(Fax,(Fay,Ha)))).
  exists Ax, Ay.
  repeat split.
  + exact Fax.
  + exact Fay.
  + intros x y Hx Hy.
    now apply Himpl, Ha.
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
  intros (Ax,(Ay,(Fax,(Fay,Ha)))) (Bx,(By,(Fbx,(Fby,Hb)))).
  exists (λ x : X, Ax x ∧ Bx x), (λ y : Y, Ay y ∧ By y).
  repeat split.
  + now apply Hand_x.
  + now apply Hand_y.
  + apply Ha.
    apply (pr1 X0).
    apply (pr1 X1).
  + apply Hb.
    apply (pr2 X0).
    apply (pr2 X1).
Qed.
Lemma filterdirprod_notempty :
  isfilter_notempty filterdirprod.
Proof.
  unfold isfilter_notempty, neg ; apply hinhuniv'.
  exact isapropempty.
  intros (Ax,(Ay,(Fax,(Fay,Ha)))).
  apply Hempty_x.
  revert Fax.
  apply Himp_x ; intros x Hx.
  apply Hempty_y.
  revert Fay.
  apply Himp_y ; intros y Hy.
  now apply (Ha x y).
Qed.

End filterdirprod.

Definition PreFilterDirprod {X Y : UU} (Fx : PreFilter X) (Fy : PreFilter Y) : PreFilter (X × Y).
Proof.
  intros X Y Fx Fy.
  simple refine (mkPreFilter _ _ _ _).
  - exact (filterdirprod Fx Fy).
  - apply filterdirprod_imply.
  - apply filterdirprod_htrue.
    apply filter_htrue.
    apply filter_htrue.
  - apply filterdirprod_and.
    apply filter_and.
    apply filter_and.
Defined.
Definition FilterDirprod {X Y : UU} (Fx : Filter X) (Fy : Filter Y) : Filter (X × Y).
Proof.
  intros X Y Fx Fy.
  refine (tpair _ _ _).
  split.
  apply (pr2 (PreFilterDirprod Fx Fy)).
  apply filterdirprod_notempty.
  apply filter_imply.
  apply filter_notempty.
  apply filter_imply.
  apply filter_notempty.
Defined.

Section filterpr1.

Context {X Y : UU}.
Context (F : (X × Y -> hProp) -> hProp)
        (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).

Definition filterpr1 : (X -> hProp) -> hProp :=
  λ A, F (λ x : X × Y, A (pr1 x)).

Lemma filterpr1_imply :
  isfilter_imply filterpr1.
Proof.
  intros A B H.
  apply Himp.
  intros x.
  now apply H.
Qed.
Lemma filterpr1_htrue :
  isfilter_htrue filterpr1.
Proof.
  now apply Htrue.
Qed.
Lemma filterpr1_and :
  isfilter_and filterpr1.
Proof.
  intros A B.
  apply Hand.
Qed.
Lemma filterpr1_notempty :
  isfilter_notempty filterpr1.
Proof.
  apply Hempty.
Qed.

End filterpr1.

Definition PreFilterPr1 {X Y : UU} (F : PreFilter (X × Y)) : PreFilter X.
Proof.
  intros X Y F.
  simple refine (mkPreFilter _ _ _ _).
  - exact (filterpr1 F).
  - apply filterpr1_imply, filter_imply.
  - apply filterpr1_htrue, filter_htrue.
  - apply filterpr1_and, filter_and.
Defined.
Definition FilterPr1 {X Y : UU} (F : Filter (X × Y)) : Filter X.
Proof.
  intros X Y F.
  refine (tpair _ _ _).
  split.
  apply (pr2 (PreFilterPr1 F)).
  apply filterpr1_notempty, filter_notempty.
Defined.

Section filterpr2.

Context {X Y : UU}.
Context (F : (X × Y -> hProp) -> hProp)
        (Himp : isfilter_imply F)
        (Htrue : isfilter_htrue F)
        (Hand : isfilter_and F)
        (Hempty : isfilter_notempty F).

Definition filterpr2 : (Y -> hProp) -> hProp :=
  λ A, F (λ x : X × Y, A (pr2 x)).

Lemma filterpr2_imply :
  isfilter_imply filterpr2.
Proof.
  intros A B H.
  apply Himp.
  intros x.
  now apply H.
Qed.
Lemma filterpr2_htrue :
  isfilter_htrue filterpr2.
Proof.
  now apply Htrue.
Qed.
Lemma filterpr2_and :
  isfilter_and filterpr2.
Proof.
  intros A B.
  apply Hand.
Qed.
Lemma filterpr2_notempty :
  isfilter_notempty filterpr2.
Proof.
  apply Hempty.
Qed.

End filterpr2.

Definition PreFilterPr2 {X Y : UU} (F : PreFilter (X × Y)) : PreFilter Y.
Proof.
  intros X Y F.
  simple refine (mkPreFilter _ _ _ _).
  - exact (filterpr2 F).
  - apply filterpr2_imply, filter_imply.
  - apply filterpr2_htrue, filter_htrue.
  - apply filterpr2_and, filter_and.
Defined.
Definition FilterPr2 {X Y : UU} (F : Filter (X × Y)) : Filter Y.
Proof.
  intros X Y F.
  refine (tpair _ _ _).
  split.
  apply (pr2 (PreFilterPr2 F)).
  apply filterpr2_notempty, filter_notempty.
Defined.

Goal ∀ {X Y : UU} (F : PreFilter (X × Y)),
    filter_le F (PreFilterDirprod (PreFilterPr1 F) (PreFilterPr2 F)).
Proof.
  intros X Y F.
  intros A.
  apply hinhuniv.
  intros (Ax,(Ay,(Fax,(Fay,Ha)))).
  simpl in * |-.
  generalize (filter_and _ _ _ Fax Fay).
  apply filter_imply.
  intros (x,y) (Fx,Fy).
  now apply Ha.
Qed.

Goal ∀ {X Y : UU} (F : PreFilter X) (G : PreFilter Y),
    filter_le (PreFilterPr1 (PreFilterDirprod F G)) F.
Proof.
  intros X Y F G.
  intros A Fa.
  apply hinhpr.
  exists A, (λ _, htrue).
  repeat split.
  - exact Fa.
  - now apply filter_htrue.
  - easy.
Qed.
Goal ∀ {X Y : UU} (F : PreFilter X) (G : PreFilter Y),
    filter_le (PreFilterPr2 (PreFilterDirprod F G)) G.
Proof.
  intros X Y F G.
  intros A Fa.
  apply hinhpr.
  exists (λ _, htrue), A.
  repeat split.
  - now apply filter_htrue.
  - exact Fa.
  - easy.
Qed.

(** ** Other filters *)

(** *** Filter on nat *)

Section filternat.

Definition filternat : (nat -> hProp) -> hProp :=
  λ P : nat -> hProp, ∃ N : nat, ∀ n : nat, N ≤ n -> P n.

Lemma filternat_imply :
  isfilter_imply filternat.
Proof.
  intros P Q H.
  apply hinhfun.
  intros (N,Hp).
  exists N.
  intros n Hn.
  now apply H, Hp.
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
  intros (Na,Ha) (Nb,Hb).
  exists (max Na Nb).
  intros n Hn.
  split.
  + apply Ha.
    eapply istransnatleh, Hn.
    now apply max_le_l.
  + apply Hb.
    eapply istransnatleh, Hn.
    now apply max_le_r.
Qed.
Lemma filternat_notempty :
  isfilter_notempty filternat.
Proof.
  intros H ; revert H.
  apply hinhuniv'.
  exact isapropempty.
  intros (N,Hn).
  apply (Hn N).
  now apply isreflnatleh.
Qed.

End filternat.

Definition FilterNat : Filter nat.
Proof.
  simple refine (mkFilter _ _ _ _ _).
  - apply filternat.
  - apply filternat_imply.
  - apply filternat_htrue.
  - apply filternat_and.
  - apply filternat_notempty.
Defined.

(** *** The upper filter *)

Section filtertop.

Context  {X : UU} (x0 : ∥ X ∥).

Definition filtertop : (X -> hProp) -> hProp :=
  λ A : X → hProp, hProppair (∀ x : X, A x) (impred_isaprop _ (λ _, propproperty _)).

Lemma filtertop_imply :
  isfilter_imply filtertop.
Proof.
  intros A B H Ha x.
  apply H, Ha.
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
  apply Ha.
  apply Hb.
Qed.
Lemma filtertop_notempty :
  isfilter_notempty filtertop.
Proof.
  intro H.
  revert x0.
  apply hinhuniv'.
  exact isapropempty.
  apply H.
Qed.

End filtertop.

Definition PreFilterTop {X : UU} : PreFilter X.
Proof.
  intros X.
  simple refine (mkPreFilter _ _ _ _).
  - exact filtertop.
  - exact filtertop_imply.
  - exact filtertop_htrue.
  - exact filtertop_and.
Defined.

Definition FilterTop {X : UU} (x0 : ∥ X ∥) : Filter X.
Proof.
  intros X x0.
  refine (tpair _ _ _).
  split.
  apply (pr2 PreFilterTop).
  apply filtertop_notempty, x0.
Defined.

Lemma PreFilterTop_correct {X : UU} :
  ∀ (F : PreFilter X), filter_le F PreFilterTop.
Proof.
  intros X F A Ha.
  apply filter_forall, Ha.
Qed.
Lemma FilterTop_correct {X : UU} :
  ∀ (x0 : ∥ X ∥) (F : Filter X), filter_le F (FilterTop x0).
Proof.
  intros X x0 F A Ha.
  apply PreFilterTop_correct, Ha.
Qed.

(** *** Intersection of filters *)

Section filterintersection.

Context {X : UU}.
Context (is : ((X -> hProp) -> hProp) -> UU).
Context (FF : (Σ F : ((X -> hProp) -> hProp), is F) -> hProp)
        (Himp : ∀ F, FF F -> isfilter_imply (pr1 F))
        (Htrue : ∀ F, FF F -> isfilter_htrue (pr1 F))
        (Hand : ∀ F, FF F -> isfilter_and (pr1 F))
        (Hempty : ∀ F, FF F -> isfilter_notempty (pr1 F)).
Context (Hff : ¬ (∀ F, ¬ FF F)).

Definition filterintersection : (X -> hProp) -> hProp :=
  λ A : X → hProp, hProppair (∀ F, FF F → (pr1 F) A)
                             (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).

Lemma filterintersection_imply :
  isfilter_imply filterintersection.
Proof.
  intros A B H Ha F Hf.
  apply (Himp F Hf A).
  apply H.
  apply Ha, Hf.
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
  apply Ha, Hf.
  apply Hb, Hf.
Qed.
Lemma filterintersection_notempty :
  isfilter_notempty filterintersection.
Proof.
  intro Hf.
  apply Hff.
  intros F Hf'.
  apply (Hempty F Hf').
  apply Hf, Hf'.
Qed.

End filterintersection.

Definition PreFilterIntersection {X : UU} (FF : PreFilter X -> hProp) : PreFilter X.
Proof.
  intros.
  simple refine (mkPreFilter _ _ _ _).
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

Definition FilterIntersection {X : UU} (FF : Filter X -> hProp) (Hff : ¬ (∀ F : Filter X, ¬ FF F)) : Filter X.
Proof.
  intros X FF Hff.
  simple refine (mkFilter _ _ _ _ _).
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
    intros F _.
    apply (filter_notempty F).
    exact Hff.
Defined.

Lemma PreFilterIntersection_glb {X : UU} (FF : PreFilter X -> hProp) :
  (∀ F : PreFilter X, FF F -> filter_le F (PreFilterIntersection FF))
× (∀ F : PreFilter X, (∀ G : PreFilter X, FF G -> filter_le G F) -> filter_le (PreFilterIntersection FF) F).
Proof.
  split.
  - intros F Hf A Ha.
    apply Ha, Hf.
  - intros F H A Fa G Hg.
    apply (H G Hg).
    apply Fa.
Qed.
Lemma FilterIntersection_glb {X : UU} (FF : Filter X -> hProp) Hff :
  (∀ F : Filter X, FF F -> filter_le F (FilterIntersection FF Hff))
× (∀ F : Filter X, (∀ G : Filter X, FF G -> filter_le G F) -> filter_le (FilterIntersection FF Hff) F).
Proof.
  split.
  - intros F Hf A Ha.
    apply Ha, Hf.
  - intros F H A Fa G Hg.
    apply (H G Hg).
    apply Fa.
Qed.

(** *** Filter generated by a set of subsets *)

Section filtergenerated.

Context {X : UU}.
Context (L : (X -> hProp) -> hProp).
Context (Hl : ∀ (L' : Sequence (X -> hProp)), (∀ m, L (L' m)) -> ¬ ∀ x : X, ¬ finite_intersection L' x).

Definition filtergenerated : (X -> hProp) -> hProp :=
  λ A : X -> hProp,
        ∃ (L' : Sequence (X -> hProp)), (∀ m, L (L' m)) × (∀ x : X, finite_intersection L' x -> A x).

Lemma filtergenerated_imply :
  isfilter_imply filtergenerated.
Proof.
  intros A B H.
  apply hinhfun ; intro Ha.
  exists (pr1 Ha), (pr1 (pr2 Ha)).
  intros x Hx.
  apply H.
  apply (pr2 (pr2 Ha)), Hx.
Qed.
Lemma filtergenerated_htrue :
  isfilter_htrue filtergenerated.
Proof.
  apply hinhpr.
  exists nil.
  split.
  intros (m,Hm).
  easy.
  easy.
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
    set (Hm := invmap (weqfromcoprodofstn (length (pr1 Ha)) (length (pr1 Hb))) m).
    change (invmap (weqfromcoprodofstn (length (pr1 Ha)) (length (pr1 Hb))) m) with Hm.
    destruct Hm.
    * rewrite coprod_rect_compute_1.
      apply (pr1 (pr2 Ha)).
    * rewrite coprod_rect_compute_2.
      apply (pr1 (pr2 Hb)).
  + intros x Hx ; simpl in Hx.
    split.
    * apply (pr2 (pr2 Ha)).
      intros m.
      specialize (Hx (weqfromcoprodofstn _ _ (ii1 m))).
      rewrite homotinvweqweq, coprod_rect_compute_1 in Hx.
      exact Hx.
    * apply (pr2 (pr2 Hb)).
      intros m.
      specialize (Hx (weqfromcoprodofstn _ _ (ii2 m))).
      rewrite homotinvweqweq, coprod_rect_compute_2 in Hx.
      exact Hx.
Qed.
Lemma filtergenerated_notempty :
  isfilter_notempty filtergenerated.
Proof.
  intro H ; revert H.
  apply hinhuniv'.
  exact isapropempty.
  intros L'.
  simple refine (Hl _ _ _).
  apply (pr1 L').
  apply (pr1 (pr2 L')).
  intros x Hx.
  refine ((pr2 (pr2 L')) _ _).
  exact Hx.
Qed.

End filtergenerated.

Definition PreFilterGenerated {X : UU} (L : (X -> hProp) -> hProp) : PreFilter X.
Proof.
  intros X L.
  simple refine (mkPreFilter _ _ _ _).
  - apply (filtergenerated L).
  - apply filtergenerated_imply.
  - apply filtergenerated_htrue.
  - apply filtergenerated_and.
Defined.

Definition FilterGenerated {X : UU} (L : (X -> hProp) -> hProp) (Hl : ∀ (L' : Sequence (X -> hProp)), (∀ m, L (L' m)) -> ¬ ∀ x : X, ¬ finite_intersection L' x) : Filter X.
Proof.
  intros X L Hl.
  exists (PreFilterGenerated L).
  split.
  apply (pr2 (PreFilterGenerated L)).
  apply filtergenerated_notempty.
  exact Hl.
Defined.

Lemma PreFilterGenerated_correct {X : UU} :
   ∀ (L : (X -> hProp) -> hProp),
   (∀ A : X -> hProp, L A -> (PreFilterGenerated L) A)
   × (∀ F : PreFilter X,
      (∀ A : X -> hProp, L A -> F A) -> filter_le F (PreFilterGenerated L)).
Proof.
  intros X L.
  split.
  - intros A La.
    apply hinhpr.
    exists (singletonSequence A).
    split.
    + easy.
    + intros x Hx.
      apply (Hx (O,,paths_refl _)).
  - intros F Hf A.
    apply hinhuniv.
    intros Ha.
    refine (filter_imply _ _ _ _ _).
    apply (pr2 (pr2 Ha)).
    apply filter_finite_intersection.
    intros m.
    apply Hf.
    apply (pr1 (pr2 Ha)).
Qed.
Lemma FilterGenerated_correct {X : UU} :
   ∀ (L : (X -> hProp) -> hProp)
   (Hl : ∀ L' : Sequence (X -> hProp),
         (∀ m, L (L' m)) ->
         ¬ (∀ x : X, ¬ finite_intersection L' x)),
   (∀ A : X -> hProp, L A -> (FilterGenerated L Hl) A)
   × (∀ F : Filter X,
      (∀ A : X -> hProp, L A -> F A) -> filter_le F (FilterGenerated L Hl)).
Proof.
  intros X L Hl.
  split.
  - intros A La.
    apply hinhpr.
    exists (singletonSequence A).
    split.
    + easy.
    + intros x Hx.
      apply (Hx (O,,paths_refl _)).
  - intros F Hf A.
    apply hinhuniv.
    intros Ha.
    refine (filter_imply _ _ _ _ _).
    apply (pr2 (pr2 Ha)).
    apply filter_finite_intersection.
    intros m.
    apply Hf.
    apply (pr1 (pr2 Ha)).
Qed.

Lemma FilterGenerated_inv {X : UU} :
   ∀ (L : (X -> hProp) -> hProp) (F : Filter X),
   (∀ A : X -> hProp, L A -> F A) ->
   ∀ (L' : Sequence (X -> hProp)),
   (∀ m, L (L' m)) ->
   ¬ (∀ x : X, ¬ finite_intersection L' x).
Proof.
  intros X.
  intros L F Hf L' Hl' H.
  apply (filter_notempty F).
  refine (filter_imply _ _ _ _ _).
  apply H.
  apply filter_finite_intersection.
  intros m.
  apply Hf, Hl'.
Qed.

Lemma ex_filter_le {X : UU} :
  ∀ (F : Filter X) (A : X -> hProp),
    (Σ G : Filter X, filter_le G F × G A)
    <-> (∀ B : X -> hProp, F B -> ¬ (∀ x : X, A x -> B x -> ∅)).
Proof.
  intros X.
  intros F A.
  split.
  - intros G B Fb H.
    simple refine (FilterGenerated_inv _ _ _ _ _ _).
    + exact X.
    + intros C.
      apply (F C ∨ C = A).
    + apply (pr1 G).
    + intros C.
      apply hinhuniv.
      intros [Fc | ->].
      apply (pr1 (pr2 G)), Fc.
      apply (pr2 (pr2 G)).
    + apply (pairSequence A B).
    + intros (m,Hm).
      apply hinhpr.
      destruct m ; simpl.
      now right.
      now left.
    + intros x.
      rewrite finite_intersection_and.
      intros H0.
      apply (H x).
      apply (pr1 H0).
      apply (pr2 H0).
  - intros H.
    simple refine (tpair _ _ _).
    simple refine (FilterGenerated _ _).
    + intros B.
      apply (F B ∨ B = A).
    + intros L Hl Hl'.
      assert (B : ∃ B : X -> hProp, F B × (∀ x, (A x ∧ B x -> A x ∧ finite_intersection L x))).
      { clear Hl' ; revert L Hl.
        apply (Sequence_rect (P := λ L : Sequence (X -> hProp),
                                    (∀ m : stn (length L), (λ B : X -> hProp, F B ∨ B = A) (L m)) ->
                                    ∃ B : X -> hProp,
                                      F B × (∀ x : X, A x ∧ B x -> A x ∧ finite_intersection L x))).
        - intros Hl.
          apply hinhpr.
          rewrite finite_intersection_htrue.
          exists (λ _, htrue).
          split.
          + apply filter_htrue.
          + easy.
        - intros L B IHl Hl.
          rewrite finite_intersection_append.
          simple refine (hinhuniv _ _).
          3: apply IHl.
          intros (C,(Fc,Hc)).
          generalize (Hl (lastelement _)) ; simpl.
          rewrite append_fun_compute_2.
          apply hinhfun.
          intros [Fl | ->].
          + refine (tpair _ _ _).
            split.
            * apply (filter_and F).
              apply Fc.
              apply Fl.
            * intros x (H0,(H1,H2)) ; repeat split.
              apply H0.
              apply H2.
              simple refine (pr2 (Hc x _)).
              split.
              apply H0.
              apply H1.
          + exists C ; split.
            * exact Fc.
            * intros x (H0,H1) ; repeat split.
              apply H0.
              apply H0.
              simple refine (pr2 (Hc x _)).
              split.
              apply H0.
              apply H1.
          + intros.
            generalize (Hl (dni_lastelement m)) ; simpl.
            now rewrite append_fun_compute_1. }
      revert B.
      apply (hinhuniv (P := hProppair _ isapropempty)).
      intros (B,(Fb,Hb)).
      apply (H B Fb).
      intros x Ax Bx.
      apply (Hl' x).
      simple refine (pr2 (Hb x _)).
      split.
      apply Ax.
      apply Bx.
    + split.
      * intros B Fb.
        apply hinhpr.
        exists (singletonSequence B).
        split.
        intros m.
        apply hinhpr.
        now left.
        intros x Hx.
        apply (Hx (O ,, paths_refl _)).
      * apply hinhpr.
        exists (singletonSequence A).
        split.
        intros m.
        apply hinhpr.
        now right.
        intros x Hx.
        apply (Hx (O ,, paths_refl _)).
Qed.

(** *** Filter defined by a base *)

Section filterbase.

Context {X : UU}.
Context (base : (X -> hProp) -> hProp)
        (Hand : ∀ A B : X -> hProp, base A -> base B -> ∃ C : X -> hProp, base C × (∀ x, C x -> A x ∧ B x))
        (Hempty : ∃ A : X -> hProp, base A)
        (Hfalse : ¬ (base (λ _, hfalse))).

Definition filterbase : (X -> hProp) -> hProp :=
  λ A : X -> hProp, (∃ B : X -> hProp, base B × ∀ x, B x -> A x).

Lemma filterbase_imply :
  isfilter_imply filterbase.
Proof.
  intros A B H.
  apply hinhfun.
  intros A'.
  exists (pr1 A').
  split.
  apply (pr1 (pr2 A')).
  intros x Hx.
  apply H.
  now apply (pr2 (pr2 A')).
Qed.
Lemma filterbase_htrue :
  isfilter_htrue filterbase.
Proof.
  revert Hempty.
  apply hinhfun.
  intros A.
  exists (pr1 A).
  split.
  apply (pr2 A).
  easy.
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
  apply (pr1 (pr2 C')).
  intros x Cx ; split.
  apply (pr2 (pr2 A')).
  now refine (pr1 (pr2 (pr2 C') _ _)).
  apply (pr2 (pr2 B')).
  now refine (pr2 (pr2 (pr2 C') _ _)).
Qed.
Lemma filterbase_notempty :
  isfilter_notempty filterbase.
Proof.
  intros H ; revert H.
  apply hinhuniv'.
  exact isapropempty.
  intros A.
  apply Hfalse.
  assert ((λ _ : X, hfalse) = (pr1 A)).
  { apply funextfun ; intro x.
    apply uahp.
    apply fromempty.
    apply (pr2 (pr2 A)). }
  rewrite X0 ; clear X0.
  apply (pr1 (pr2 A)).
Qed.

End filterbase.

Definition PreFilterBase {X : UU} (base : (X -> hProp) -> hProp) (Hand : ∀ A B : X -> hProp, base A -> base B -> ∃ C : X -> hProp, base C × (∀ x, C x -> A x ∧ B x)) (Hempty : ∃ A : X -> hProp, base A) : PreFilter X.
Proof.
  intros.
  simple refine (mkPreFilter _ _ _ _).
  - apply (filterbase base).
  - apply filterbase_imply.
  - apply filterbase_htrue, Hempty.
  - apply filterbase_and, Hand.
Defined.
Definition FilterBase {X : UU} (base : (X -> hProp) -> hProp) (Hand : ∀ A B : X -> hProp, base A -> base B -> ∃ C : X -> hProp, base C × (∀ x, C x -> A x ∧ B x)) (Hempty : ∃ A : X -> hProp, base A) (Hfalse : ¬ (base (λ _, hfalse))) : Filter X.
Proof.
  intros.
  exists (filterbase base).
  split.
  simple refine (pr2 (PreFilterBase _ _ _)).
  exact Hand.
  exact Hempty.
  apply filterbase_notempty.
  exact Hfalse.
Defined.
