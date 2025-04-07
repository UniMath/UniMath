(** ** More results on sets *)

Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.Foundations.Sets.

(** ** Contents

  - (More entries need to be added here...)
  - An equality lemma for elements of a carrier type [carrier_eq]
  - Other universal properties for [setquot]
  - The trivial equivalence relation on the unit type
  - The equivalence relation of being in the same fiber
  - Subsets
  - Binary relations
 *)

Local Open Scope logic.

Definition hProp_set : hSet := make_hSet _ isasethProp.

Definition isconst {X:UU} {Y:hSet} (f : X -> Y) : hProp := ∀ x x', f x = f x'.

Lemma carrier_eq
  {X : UU}
  {A : hsubtype X}
  (x y : A)
  (H : pr1 x = pr1 y)
  : x = y.
Proof.
  apply subtypePath.
  {
    intro.
    apply propproperty.
  }
  exact H.
Qed.

Definition squash_to_hSet {X : UU} {Y : hSet} (f : X -> Y) : isconst f -> ∥ X ∥ -> Y.
Proof.
  apply squash_to_set, setproperty.
Defined.

Definition isconst_2 {X Y:UU} {Z:hSet} (f : X -> Y -> Z) : hProp :=
  ∀ x x' y y', f x y = f x' y'.

Definition squash_to_hSet_2 {X Y : UU} {Z : hSet} (f : X -> Y -> Z) :
  isconst_2 f -> ∥ X ∥ -> ∥ Y ∥ -> Z.
Proof.
  intros c. use squash_to_set.
  { apply isaset_forall_hSet. }
  { intros x. use squash_to_hSet. exact (f x). intros y y'. exact (c x x y y'). }
  { intros x x'. apply funextfun; intros yn.
    apply (squash_to_prop yn).
    { apply setproperty. }
    intros y. assert (e : hinhpr y = yn).
    { apply propproperty. }
    induction e. change ( f x y = f x' y ). exact (c x x' y y). }
Defined.

Definition isconst_2' {X Y:UU} {Z:hSet} (f : X -> Y -> Z) : hProp :=
    (∀ x x' y, f x y = f x' y)
    ∧
    (∀ x y y', f x y = f x y').

Definition squash_to_hSet_2' {X Y : UU} {Z : hSet} (f : X -> Y -> Z) :
  isconst_2' f -> ∥ X ∥ -> ∥ Y ∥ -> Z.
Proof.
  intros [c d]. use squash_to_set.
  { apply isaset_forall_hSet. }
  { intros x. use squash_to_hSet. exact (f x). intros y y'. exact (d x y y'). }
  { intros x x'. apply funextfun; intros yn.
    apply (squash_to_prop yn).
    { apply setproperty. }
    intros y. assert (e : hinhpr y = yn).
    { apply propproperty. }
    induction e. change ( f x y = f x' y ). exact (c x x' y). }
Defined.

Definition eqset_to_path {X:hSet} (x y:X) : eqset x y -> paths x y := λ e, e.

Lemma isapropiscomprelfun {X : UU} {Y : hSet} (R : hrel X) (f : X -> Y) : isaprop (iscomprelfun R f).
Proof.
  apply impred. intro x. apply impred. intro x'. apply impred. intro r. apply Y.
Defined.

Lemma iscomprelfun_funcomp {X Y Z : UU} {R : hrel X} {S : hrel Y}
           {f : X → Y} {g : Y → Z} (Hf : iscomprelrelfun R S f) (Hg : iscomprelfun S g) :
  iscomprelfun R (g ∘ f).
Proof.
  intros x x' r. exact (Hg _ _ (Hf x x' r)).
Defined.

Definition fun_hrel_comp {X Y : UU} (f : X → Y) (gt : hrel Y) : hrel X :=
  λ x y : X, gt (f x) (f y).

(** ** Other universal properties for [setquot] *)

Theorem setquotunivprop' {X : UU} {R : eqrel X} (P : setquot (pr1 R) -> UU)
        (H : ∏ x, isaprop (P x)) (ps : ∏ x : X, P (setquotpr R x)) : ∏ c : setquot (pr1 R), P c.
Proof.
  exact (setquotunivprop R (λ x, make_hProp (P x) (H x)) ps).
Defined.

Theorem setquotuniv2prop' {X : UU} {R : eqrel X} (P : setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2, isaprop (P x1 x2))
        (ps : ∏ x1 x2, P (setquotpr R x1) (setquotpr R x2)) : ∏ c1 c2 : setquot (pr1 R), P c1 c2.
Proof.
  exact (setquotuniv2prop R (λ x1 x2, make_hProp (P x1 x2) (H x1 x2)) ps).
Defined.

Theorem setquotuniv3prop' {X : UU} {R : eqrel X}
        (P : setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2 x3, isaprop (P x1 x2 x3))
        (ps : ∏ x1 x2 x3, P (setquotpr R x1) (setquotpr R x2) (setquotpr R x3)) :
  ∏ c1 c2 c3 : setquot (pr1 R), P c1 c2 c3.
Proof.
  exact (setquotuniv3prop R (λ x1 x2 x3, make_hProp (P x1 x2 x3) (H x1 x2 x3)) ps).
Defined.

Theorem setquotuniv4prop' {X : UU} {R : eqrel X}
        (P : setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2 x3 x4, isaprop (P x1 x2 x3 x4))
        (ps : ∏ x1 x2 x3 x4,
              P (setquotpr R x1) (setquotpr R x2) (setquotpr R x3) (setquotpr R x4)) :
  ∏ c1 c2 c3 c4 : setquot (pr1 R), P c1 c2 c3 c4.
Proof.
  exact (setquotuniv4prop R (λ x1 x2 x3 x4, make_hProp (P x1 x2 x3 x4) (H x1 x2 x3 x4)) ps).
Defined.

(** ** The trivial equivalence relation on the unit type*)
Definition unittrivialrel : hrel unit := λ _ _, htrue.

Lemma iseqrelunittrivialrel : iseqrel unittrivialrel.
Proof.
  use iseqrelconstr.
  - intros ? ? ? ? ?. exact tt.
  - intros ?. exact tt.
  - intros ? ? ?. exact tt.
Qed.

Definition uniteqrel : eqrel unit := unittrivialrel,,iseqrelunittrivialrel.

Definition unittrivialrel_iseqclasstotalsubtype : iseqclass uniteqrel (totalsubtype unit).
Proof.
  use iseqclassconstr.
  - use hinhpr.
    use (invmap (weqtotalsubtype _)).
    exact tt.
  - intros _ ? _ _.
    exact tt.
  - intros ? ? _ _.
    exact tt.
Qed.

Definition unittrivialrel_setquot := totalsubtype unit ,, unittrivialrel_iseqclasstotalsubtype.

Lemma unittrivialrel_setquot_eq (c : setquot uniteqrel) : totalsubtype unit = c.
Proof.
  use funextsec.
  intro t.
  induction t.
  cbn.
  use hPropUnivalence.
  - intros _ .
    induction c as [c iseqclass].
    induction iseqclass as [ishinh is].
    use (squash_to_hProp ishinh).
    intro t.
    induction t as [t tinc].
    induction t.
    exact tinc.
  - intros _.
    exact tt.
Qed.

Lemma iscontr_setquotuniteqrel : iscontr (setquot uniteqrel).
Proof.
  use make_iscontr.
  - exact unittrivialrel_setquot.
  - intro c.
    use pathsinv0.
    use subtypePath.
    + use isapropiseqclass.
    + use unittrivialrel_setquot_eq.
Qed.

(** ** The equivalence relation of being in the same fiber *)

Definition same_fiber_eqrel {X Y : hSet} (f : X → Y) : eqrel X.
Proof.
  use make_eqrel.
  - intros x y.
    exact ((f x) = (f y)).
  - use iseqrelconstr.
    + intros ? ? ? xy yz; exact (xy @ yz).
    + intro; reflexivity.
    + intros ? ? eq; exact (!eq).
Defined.

(** ** Subsets *)

Definition pi0 (X : UU) : hSet := setquotinset (pathseqrel X).

Section Pi0.
  Definition π₀ : Type -> hSet := pi0.
  Definition component {X:Type} : X -> π₀ X := setquotpr (pathseqrel X).
  Definition π₀_map {X Y:Type} : (X -> Y) -> (π₀ X -> π₀ Y)
    := λ f, setquotfun (pathseqrel X) (pathseqrel Y) f (λ x x', hinhfun (maponpaths f)).
  Definition π₀_universal_property {X:Type} {Y:hSet} : (π₀ X -> Y) ≃ (X -> Y).
  Proof.
    exists (λ h, h ∘ component). intros f. apply iscontraprop1.
    - apply isaproptotal2.
      + intros h. use (_ : isaset _). apply impred_isaset. intros x. apply setproperty.
      + intros h h' e e'. apply funextsec. intro w.
        { apply (surjectionisepitosets component).
          - apply issurjsetquotpr.
          - apply setproperty.
          - intros x. exact (maponpaths (λ k, k x) (e @ ! e')). }
    - now exists (setquotuniv _ _ f (λ x y e, squash_to_prop e (setproperty Y (f x) (f y)) (maponpaths f))).
  Defined.
  Definition π₀_universal_map {X:Type} {Y:hSet} : (X -> Y) -> (π₀ X -> Y) := invmap π₀_universal_property.
  Lemma π₀_universal_map_eqn {X:Type} {Y:hSet} (f : X -> Y) :
    ∏ (x:X), π₀_universal_map f (component x) = f x.
  Proof.
    reflexivity.
  Defined.
  Lemma π₀_universal_map_uniq {X:Type} {Y:hSet} (h h' : π₀ X -> Y) :
    (∏ x, h (component x) = h' (component x)) -> h ~ h'.
  Proof.
    intros e x. apply (surjectionisepitosets component).
    - apply issurjsetquotpr.
    - apply setproperty.
    - exact e.
  Defined.
End Pi0.


(** ** Minimal equivalence relations *)
(* Constructs the smallest eqrel containing a given relation *)
Section mineqrel.

  Close Scope set.

  Context {A : UU} (R0 : hrel A).

  Lemma isaprop_eqrel_from_hrel a b :
    isaprop (∏ R : eqrel A, (∏ x y, R0 x y -> R x y) -> R a b).
  Proof.
    apply impred; intro R; apply impred_prop.
  Qed.

  Definition eqrel_from_hrel : hrel A :=
    λ a b, make_hProp _ (isaprop_eqrel_from_hrel a b).

  Lemma iseqrel_eqrel_from_hrel : iseqrel eqrel_from_hrel.
  Proof.
    repeat split.
    - intros x y z H1 H2 R HR. exact (eqreltrans _ _ _ _ (H1 _ HR) (H2 _ HR)).
    - now intros x R _; apply (eqrelrefl R).
    - intros x y H R H'. exact (eqrelsymm _ _ _ (H _ H')).
  Qed.

  Lemma eqrel_impl a b : R0 a b -> eqrel_from_hrel a b.
  Proof.
    now intros H R HR; apply HR.
  Qed.

  (* eqrel_from_hrel is the *smallest* relation containing R0 *)
  Lemma minimal_eqrel_from_hrel (R : eqrel A) (H : ∏ a b, R0 a b -> R a b) :
    ∏ a b, eqrel_from_hrel a b -> R a b.
  Proof.
    now intros a b H'; apply (H' _ H).
  Qed.

End mineqrel.

Definition maphrel
  {X X' : UU}
  (f : X → X')
  (R : hrel X')
  : hrel X
  := λ x x', R (f x) (f x').

Lemma mapeqrel_iseqrel
  {X X' : UU}
  (f : X → X')
  (R : eqrel X')
  : iseqrel (maphrel f R).
Proof.
  repeat split.
  - intros x x' x''.
    apply eqreltrans.
  - intro x.
    apply eqrelrefl.
  - intros x y.
    apply eqrelsymm.
Qed.

Definition mapeqrel
  {X X' : UU}
  (f : X → X')
  (R : eqrel X')
  : eqrel X
  := make_eqrel _ (mapeqrel_iseqrel f R).

Lemma iscomprelrelfun_eqrel_from_hrel
  (X X' : UU)
  (R : hrel X)
  (R' : hrel X')
  (f : X → X')
  (Hf : iscomprelrelfun R R' f)
  : iscomprelrelfun (eqrel_from_hrel R) (eqrel_from_hrel R') f.
Proof.
  intros x x' Hx.
  intros R0 HR0.
  apply (Hx (mapeqrel f R0)).
  intros y y' Hy.
  apply HR0.
  apply Hf.
  apply Hy.
Qed.

Definition prod_eqrel_pr1
  {X X' : UU}
  (R : eqrel (X × X'))
  (x' : X')
  : eqrel X.
Proof.
  use ((λ x y, R (x ,, x') (y ,, x')) ,, _).
  abstract (
    repeat split;
    [ intros z z' z'';
      apply eqreltrans
    | intros z;
      apply eqrelrefl
    | intros z z';
      apply eqrelsymm ]
  ).
Defined.

Definition prod_eqrel_pr2
  {X X' : UU}
  (R : eqrel (X × X'))
  (x : X)
  : eqrel X'.
Proof.
  use ((λ x' y', R (x ,, x') (x ,, y')) ,, _).
  abstract (
    repeat split;
    [ intros z z' z'';
      apply eqreltrans
    | intros z;
      apply eqrelrefl
    | intros z z';
      apply eqrelsymm ]
  ).
Defined.

(* The conditions are sufficient and necessary. Consider, for example, the zero relation. *)
Lemma eqrel_from_hreldirprod
  {X X' : UU}
  (R : hrel X)
  (R' : hrel X')
  (HR : isrefl R)
  (HR' : isrefl R')
  : eqrel_from_hrel (hreldirprod R R') = hreldirprod (eqrel_from_hrel R) (eqrel_from_hrel R').
Proof.
  apply funextfun.
  intro x.
  apply funextfun.
  intro x'.
  apply weqtopathshProp.
  apply logeqweq.
  - refine (minimal_eqrel_from_hrel _ (eqreldirprod (make_eqrel _ (iseqrel_eqrel_from_hrel _)) (make_eqrel _ (iseqrel_eqrel_from_hrel _))) _ _ _).
    intros y y' Hy.
    induction Hy as [Hy1 Hy2].
    split;
      apply eqrel_impl;
      easy.
  - intros Hx R0 H.
    induction Hx as [Hx1 Hx2].
    refine (eqreltrans R0 _ _ _
      (Hx1 (prod_eqrel_pr1 R0 (pr2 x)) _)
      (Hx2 (prod_eqrel_pr2 R0 (pr1 x')) _)).
    + intros y y' Hy.
      apply H.
      split.
      * exact Hy.
      * apply HR'.
    + intros y y' Hy.
      apply H.
      split.
      * apply HR.
      * exact Hy.
Qed.

Lemma eqreleq {A : UU} (R : eqrel A) (x y : A) : x = y → R x y.
Proof.
  intros e.
  induction e.
  apply eqrelrefl.
Defined.

(** * Additional lemmas on binary relations *)

Lemma isaprop_isirrefl {X : UU} (rel : hrel X) :
  isaprop (isirrefl rel).
Proof.
  apply impred_isaprop ; intro.
  now apply isapropneg.
Qed.
Lemma isaprop_issymm {X : UU} (rel : hrel X) :
  isaprop (issymm rel).
Proof.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply isapropimpl.
  now apply pr2.
Qed.
Lemma isaprop_iscotrans {X : UU} (rel : hrel X) :
  isaprop (iscotrans rel).
Proof.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply impred_isaprop ; intro z.
  apply isapropimpl.
  now apply pr2.
Qed.

(*Accessor to iseqrel from eqrel*)
Definition iseqreleqrel {X : UU} (R : eqrel X) : iseqrel R := pr2 R.

Definition iseqreldirprod {X Y : UU} (RX : hrel X) (RY : hrel Y)
           (isx : iseqrel RX) (isy : iseqrel RY) :
  iseqrel (hreldirprod RX RY)
  := pr2 (eqreldirprod (RX,,isx) (RY,,isy)).

(**
 Useful functions for when using univalence of sets
 *)
Definition univalence_hSet
           {X Y : hSet}
           (w : X ≃ Y)
  : X = Y
  := invmap (hSet_univalence _ _) w.

Definition hSet_univalence_map_univalence_hSet
           {X Y : hSet}
           (w : X ≃ Y)
  : hSet_univalence_map X Y (univalence_hSet w) = w.
Proof.
  exact (homotweqinvweq (hSet_univalence _ _) w).
Defined.

Definition hSet_univalence_univalence_hSet_map
           {X Y : hSet}
           (p : X = Y)
  : univalence_hSet (hSet_univalence_map X Y p) = p.
Proof.
  exact (homotinvweqweq (hSet_univalence _ _) p).
Qed.

Definition univalence_hSet_idweq
           (X : hSet)
  : univalence_hSet (idweq X) = idpath X.
Proof.
  refine (_ @ hSet_univalence_univalence_hSet_map (idpath _)).
  apply maponpaths.
  apply idpath.
Defined.

Definition hSet_univalence_map_inv
           {X Y : hSet}
           (p : X = Y)
  : hSet_univalence_map _ _ (!p) = invweq (hSet_univalence_map _ _ p).
Proof.
  induction p.
  cbn.
  use subtypePath.
  {
    intro.
    apply isapropisweq.
  }
  apply idpath.
Qed.

Definition univalence_hSet_inv
           {X Y : hSet}
           (w : X ≃ Y)
  : !(univalence_hSet w) = univalence_hSet (invweq w).
Proof.
  refine (!(hSet_univalence_univalence_hSet_map _) @ _).
  apply maponpaths.
  rewrite hSet_univalence_map_inv.
  rewrite hSet_univalence_map_univalence_hSet.
  apply idpath.
Qed.
