(** * Results about Filters *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Complements.
Require Import UniMath.Dedekind.Complements.

(** ** Definition of a Filter *)

Section Filter_def.

Context {X : UU}.
Context (F : (X -> hProp) -> hProp).

Definition isfilter_imply : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ A B : X -> hProp, (∀ x : X, A x -> B x) -> F A -> F B).
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropimpl.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition isfilter_finite_intersection : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ (L : Sequence (X -> hProp)), (∀ n, F (L n)) -> F (finite_intersection L)).
  apply impred_isaprop ; intros L.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition isfilter_notempty : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (¬ F (λ _ : X, hfalse)).
  apply isapropneg.
Defined.

Definition isfilter : hProp :=
  isfilter_imply ∧ isfilter_finite_intersection ∧ isfilter_notempty.

Lemma isfilter_finite_intersection_htrue :
  isfilter_finite_intersection -> F (λ _ : X, htrue).
Proof.
  intros Hand.
  rewrite <- finite_intersection_htrue.
  apply Hand.
  intros (m,Hm).
  apply fromempty.
  revert Hm.
  now apply negnatlthn0.
Qed.

Lemma isfilter_finite_intersection_and :
  isfilter_finite_intersection -> ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x).
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
  F (λ _, htrue) -> (∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x))
  -> isfilter_finite_intersection.
Proof.
  intros Htrue Hand L.
  apply (pr2 (finite_intersection_hProp F)).
  split.
  - exact Htrue.
  - exact Hand.
Qed.

End Filter_def.

Lemma emptynofilter :
  ∀ F : (empty -> hProp) -> hProp,
    ¬ isfilter F.
Proof.
  intros F (Himp,(Hand,Hempty)).
  apply Hempty.
  apply isfilter_finite_intersection_htrue in Hand.
  assert ((λ _ : ∅, hfalse) = (λ _ : ∅, htrue)).
  apply funextfun, fromempty.
  rewrite X.
  exact Hand.
Qed.

Definition Filter (X : UU) := Σ F : (X -> hProp) -> hProp, isfilter F.
Definition pr1Filter (X : UU) (F : Filter X) : (X -> hProp) -> hProp := pr1 F.
Coercion pr1Filter : Filter >-> Funclass.

Definition mkFilter {X : UU} (F : (X -> hProp) -> hProp) (Himp : isfilter_imply F) (Htrue : F (λ _ : X, htrue)) (Hand : ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x)) (Hempty : isfilter_notempty F) : Filter X :=
  F ,, Himp ,, (isfilter_finite_intersection_carac F Htrue Hand) ,, Hempty.

Section Filter_pty.

Context {X : UU}.
Context (F : Filter X).

Lemma filter_imply :
  isfilter_imply F.
Proof.
  exact (pr1 (pr2 F)).
Qed.
Lemma filter_finite_intersection :
  isfilter_finite_intersection F.
Proof.
  exact (pr1 (pr2 (pr2 F))).
Qed.
Lemma filter_htrue :
  F (λ _ : X, htrue).
Proof.
  apply isfilter_finite_intersection_htrue.
  exact filter_finite_intersection.
Qed.
Lemma filter_and :
  ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x).
Proof.
  apply isfilter_finite_intersection_and.
  exact filter_finite_intersection.
Qed.
Lemma filter_notempty :
  isfilter_notempty F.
Proof.
  exact (pr2 (pr2 (pr2 F))).
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

Lemma isasetFilter (X : UU) : isaset (Filter X).
Proof.
  intros X.
  simple refine (isaset_total2_subset (hSetpair _ _) _).
  apply impred_isaset ; intros _.
  apply isasethProp.
Qed.

(** *** Order on filters *)

Definition filter_le {X : UU} (F G : Filter X) :=
  ∀ A : X -> hProp, G A -> F A.

Lemma istrans_filter_le {X : UU} :
  ∀ F G H : Filter X,
    filter_le F G -> filter_le G H -> filter_le F H.
Proof.
  intros X.
  intros F G H Hfg Hgh A Fa.
  apply Hfg, Hgh, Fa.
Qed.
Lemma isrefl_filter_le {X : UU} :
  ∀ F : Filter X, filter_le F F.
Proof.
  intros X F A Fa.
  exact Fa.
Qed.
Lemma isantisymm_filter_le {X : UU} :
  ∀ F G : Filter X, filter_le F G -> filter_le G F -> F = G.
Proof.
  intros X F G Hle Hge.
  apply subtypeEquality_prop.
  apply funextfun ; intros A.
  apply uahp.
  now apply Hge.
  now apply Hle.
Qed.

Definition PartialOrder_filter_le (X : UU) : PartialOrder (hSetpair (Filter _) (isasetFilter X)).
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

Definition filtermap {X Y : UU} (f : X -> Y) (F : Filter X) : Filter Y.
Proof.
  intros X Y f F.
  simple refine (mkFilter _ _ _ _ _).
  - apply (λ A : (Y -> hProp), F (λ x : X, A (f x))).
  - intros A B Himp.
    apply filter_imply.
    intros x.
    apply Himp.
  - apply filter_htrue.
  - intros A B.
    apply filter_and.
  - apply filter_notempty.
Defined.

Lemma filtermap_incr {X Y : UU} :
  ∀ (f : X -> Y) (F G : Filter X),
    filter_le F G -> filter_le (filtermap f F) (filtermap f G).
Proof.
  intros X Y.
  intros f F G Hle A ; simpl.
  apply Hle.
Qed.

(** *** Limit: filter version *)

Definition filterlim {X Y : UU} (f : X -> Y) (F : Filter X) (G : Filter Y) :=
  filter_le (filtermap f F) G.

Lemma filterlim_comp {X Y Z : UU} :
  ∀ (f : X -> Y) (g : Y -> Z)
    (F : Filter X) (G : Filter Y) (H : Filter Z),
    filterlim f F G -> filterlim g G H -> filterlim (λ x : X, g (f x)) F H.
Proof.
  intros X Y Z.
  intros f g F G H Hf Hg A Fa.
  specialize (Hg _ Fa).
  specialize (Hf _ Hg).
  apply Hf.
Qed.

Lemma filterlim_decr_1 {X Y : UU} :
  ∀ (f : X -> Y) (F F' : Filter X) (G : Filter Y),
    filter_le F' F -> filterlim f F G -> filterlim f F' G.
Proof.
  intros X Y.
  intros f F F' G Hf Hle A Ha.
  specialize (Hle _ Ha).
  specialize (Hf _ Hle).
  apply Hf.
Qed.

Lemma filterlim_incr_2 {X Y : UU} :
  ∀ (f : X -> Y) (F : Filter X) (G G' : Filter Y),
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

Definition filter_dom {X : UU} (F : Filter X) (dom : X -> hProp) (Hdom : ∀ P, F P -> ¬ ¬ ∃ x, dom x ∧ P x) :
  Filter X.
Proof.
  intros X F dom Hdom.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (pr1 F).
    intros x.
    simple refine (hProppair _ _).
    apply (dom x -> A x).
    apply isapropimpl.
    now apply propproperty.
  - simpl ; intros A B Himpl.
    apply filter_imply.
    intros x Ax Hx.
    apply Himpl, Ax, Hx.
  - apply filter_forall.
    intros x Hx.
    exact tt.
  - simpl ; intros A B Ha Hb.
    generalize (filter_and _ _ _ Ha Hb).
    apply filter_imply.
    intros x (Ax,Bx) Hx.
    split.
    + apply Ax, Hx.
    + apply Bx, Hx.
  - simpl.
    intro Hf.
    apply Hdom in Hf.
    apply Hf.
    unfold neg.
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros (x,(Hx,Hx')).
    now apply Hx'.
Defined.

Definition filter_subtypes {X : UU} (F : Filter X) (dom : X -> hProp) (Hdom : ¬ F (λ x : X, hneg (dom x))) :
  Filter (Σ x : X, dom x).
Proof.
  intros X F dom Hdom.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (pr1 F).
    intros x.
    simple refine (hProppair _ _).
    + apply (∀ (Hx : dom x), A (x,,Hx)).
    + apply impred_isaprop ; intros Hx.
      now apply propproperty.
  - simpl ; intros A B Himpl.
    apply filter_imply.
    intros x Ax Hx.
    apply Himpl, Ax.
  - apply filter_forall.
    intros x Hx.
    exact tt.
  - simpl ; intros A B Ha Hb.
    generalize (filter_and _ _ _ Ha Hb).
    apply filter_imply.
    intros x (Ax,Bx) Hx.
    split.
    + apply Ax.
    + apply Bx.
  - simpl.
    intro Hf.
    apply Hdom.
    revert Hf.
    apply filter_imply.
    intros x Hx H.
    now apply Hx.
Defined.

(** *** Product of filters *)

Definition filter_prod {X Y : UU} (Fx : Filter X) (Fy : Filter Y) : Filter (X × Y).
Proof.
  intros X Y Fx Fy.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (∃ (Ax : X -> hProp) (Ay : Y -> hProp), Fx Ax × Fy Ay × (∀ (x : X) (y : Y), Ax x -> Ay y -> A (x,,y))).
  - intros A B Himpl.
    apply hinhfun.
    intros (Ax,(Ay,(Fax,(Fay,Ha)))).
    exists Ax, Ay.
    repeat split.
    + exact Fax.
    + exact Fay.
    + intros x y Hx Hy.
      now apply Himpl, Ha.
  - apply hinhpr.
    exists (λ _:X, htrue), (λ _:Y, htrue).
    repeat split.
    + apply filter_htrue.
    + apply filter_htrue.
  - intros A B.
    apply hinhfun2.
    intros (Ax,(Ay,(Fax,(Fay,Ha)))) (Bx,(By,(Fbx,(Fby,Hb)))).
    exists (λ x : X, Ax x ∧ Bx x), (λ y : Y, Ay y ∧ By y).
    repeat split.
    + now apply filter_and.
    + now apply filter_and.
    + apply Ha.
      apply (pr1 X0).
      apply (pr1 X1).
    + apply Hb.
      apply (pr2 X0).
      apply (pr2 X1).
  - simpl ; unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
    intros (Ax,(Ay,(Fax,(Fay,Ha)))).
    apply (filter_notempty Fx).
    revert Fax.
    apply filter_imply ; intros x Hx.
    apply (filter_notempty Fy).
    revert Fay.
    apply filter_imply ; intros y Hy.
    now apply (Ha x y).
Defined.

Definition filter_pr1 {X Y : UU} (F : Filter (X × Y)) : Filter X.
Proof.
  intros X Y F.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (F (λ x : X × Y, A (pr1 x))).
  - intros A B H.
    apply filter_imply.
    intros x.
    now apply H.
  - simpl.
    now apply filter_htrue.
  - intros A B.
    apply filter_and.
  - apply filter_notempty.
Defined.

Definition filter_pr2 {X Y : UU} (F : Filter (X × Y)) : Filter Y.
Proof.
  intros X Y F.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (F (λ x : X × Y, A (pr2 x))).
  - intros A B H.
    apply filter_imply.
    intros x.
    now apply H.
  - simpl.
    now apply filter_htrue.
  - intros A B.
    apply filter_and.
  - apply filter_notempty.
Defined.

Goal ∀ {X Y : UU} (F : Filter (X × Y)),
    filter_le F (filter_prod (filter_pr1 F) (filter_pr2 F)).
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

Goal ∀ {X Y : UU} (F : Filter X) (G : Filter Y),
    filter_le (filter_pr1 (filter_prod F G)) F.
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
Goal ∀ {X Y : UU} (F : Filter X) (G : Filter Y),
    filter_le (filter_pr2 (filter_prod F G)) G.
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

Definition filter_nat : Filter nat.
Proof.
  simple refine (mkFilter _ _ _ _ _).
  - intros P.
    apply (∃ N : nat, ∀ n : nat, N ≤ n -> P n).
  - intros P Q H.
    apply hinhfun.
    intros (N,Hp).
    exists N.
    intros n Hn.
    now apply H, Hp.
  - apply hinhpr.
    now exists O.
  - intros A B.
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
  - intros H ; revert H.
    apply hinhuniv'.
    exact isapropempty.
    intros (N,Hn).
    apply (Hn (S N)).
    now apply natlehnsn.
Defined.

(** *** The smallest filter *)

Definition filter_top {X : UU} (x0 : ∥ X ∥) : Filter X.
Proof.
  intros X x0.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    simple refine (hProppair _ _).
    apply (∀ x, A x).
    apply impred_isaprop ; intros x.
    apply propproperty.
  - simpl ; intros A B H Ha x.
    apply H, Ha.
  - simpl ; intros x.
    apply tt.
  - simpl ; intros A B Ha Hb x.
    split.
    apply Ha.
    apply Hb.
  - simpl ; intro H.
    revert x0.
    apply hinhuniv'.
    exact isapropempty.
    apply H.
Defined.

Lemma filter_top_correct {X : UU} :
  ∀ (x0 : ∥ X ∥) (F : Filter X), filter_le F (filter_top x0).
Proof.
  intros X x0 F A Ha.
  apply filter_forall, Ha.
Qed.

(** *** Intersection of filters *)

Definition filter_intersection {X : UU} (FF : Filter X -> hProp) (Hff : ¬ (∀ F : Filter X, ¬ FF F)) : Filter X.
Proof.
  intros X FF Hff.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    simple refine (hProppair _ _).
    apply (∀ F : Filter _, FF F -> F A).
    apply impred_isaprop ; intros F.
    apply isapropimpl.
    apply propproperty.
  - simpl ; intros A B H Ha F Hf.
    refine (filter_imply _ _ _ _ _).
    apply H.
    apply Ha, Hf.
  - simpl ; intros F Hf.
    now apply filter_htrue.
  - simpl ; intros A B Ha Hb F Hf.
    apply filter_and.
    apply Ha, Hf.
    apply Hb, Hf.
  - simpl ; intro Hf.
    apply Hff.
    intros F Hf'.
    apply (filter_notempty F).
    apply Hf, Hf'.
Defined.

Lemma filter_intersection_glb {X : UU} (FF : Filter X -> hProp) (Hff : ¬ (∀ F : Filter X, ¬ FF F)) :
  (∀ F : Filter X, FF F -> filter_le F (filter_intersection FF Hff))
× (∀ F : Filter X, (∀ G : Filter X, FF G -> filter_le G F) -> filter_le (filter_intersection FF Hff) F).
Proof.
  split.
  - intros F Hf A Ha.
    apply Ha.
    exact Hf.
  - intros F H A Fa G Hg.
    apply H.
    apply Hg.
    apply Fa.
Qed.

(** *** Filter generated by a set of subsets *)

Definition generated_filter {X : UU} (L : (X -> hProp) -> hProp) (Hl : ∀ (L' : Sequence (X -> hProp)), (∀ m, L (L' m)) -> ¬ ∀ x : X, ¬ finite_intersection L' x) : Filter X.
Proof.
  intros X L Hl.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (∃ (L' : Sequence (X -> hProp)), (∀ m, L (L' m)) × (∀ x : X, finite_intersection L' x -> A x)).
  - intros A B H.
    apply hinhfun ; intro Ha.
    exists (pr1 Ha), (pr1 (pr2 Ha)).
    intros x Hx.
    apply H.
    apply (pr2 (pr2 Ha)), Hx.
  - apply hinhpr.
    exists nil.
    split.
    intros (m,Hm).
    easy.
    easy.
  - intros A B.
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
  - intro H ; revert H.
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros L'.
    simple refine (Hl _ _ _).
    apply (pr1 L').
    apply (pr1 (pr2 L')).
    intros x Hx.
    refine ((pr2 (pr2 L')) _ _).
    exact Hx.
Defined.

Lemma generated_filter_correct {X : UU} :
   ∀ (L : (X -> hProp) -> hProp)
   (Hl : ∀ L' : Sequence (X -> hProp),
         (∀ m, L (L' m)) ->
         ¬ (∀ x : X, ¬ finite_intersection L' x)),
   (∀ A : X -> hProp, L A -> (generated_filter L Hl) A)
   × (∀ F : Filter X,
      (∀ A : X -> hProp, L A -> F A) -> filter_le F (generated_filter L Hl)).
Proof.
  intros L Hl.
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

Lemma generated_filter_inv {X : UU} :
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
    simple refine (generated_filter_inv _ _ _ _ _ _).
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
    simple refine (generated_filter _ _).
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
            * apply filter_and.
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

Definition base_filter {X : UU} (x0 : ∥ X ∥) (base : (X -> hProp) -> hProp) (Hand : ∀ A B : X -> hProp, base A -> base B -> ∃ C : X -> hProp, base C × (∀ x, C x -> A x ∧ B x)) (Hempty : ∃ A : X -> hProp, base A) (Hfalse : ¬ (base (λ _, hfalse))) : Filter X.
Proof.
  intros X x0 base Hand Hempty Hfalse.
  simple refine (mkFilter _ _ _ _ _).
  - intros A.
    apply (∃ B : X -> hProp, base B × ∀ x, B x -> A x).
  - intros A B H.
    apply hinhfun.
    intros A'.
    exists (pr1 A').
    split.
    apply (pr1 (pr2 A')).
    intros x Hx.
    apply H.
    now apply (pr2 (pr2 A')).
  - revert Hempty.
    apply hinhfun.
    intros A.
    exists (pr1 A).
    split.
    apply (pr2 A).
    easy.
  - intros A B.
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
  - intros H ; revert H.
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
Defined.
