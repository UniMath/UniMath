Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.

Declare Scope subtype.
Delimit Scope subtype with subtype.

Local Open Scope subtype.

Local Open Scope logic.
Local Open Scope type.

(** The powerset, or set of all subsets, of a set. *)
Definition subtype_set X : hSet := make_hSet (hsubtype X) (isasethsubtype X).

Definition subtype_isIn {X:UU} {S:hsubtype X} (s:S) (T:hsubtype X) : hProp := T (pr1 s).

Notation " s ∈ T " := (subtype_isIn s T) (at level 70) : subtype.

Notation " s ∉ T " := (¬ (subtype_isIn s T) : hProp) (at level 70) : subtype.

Definition subtype_containedIn {X:UU} : hrel (subtype_set X) := λ S T, ∀ x:X, S x ⇒ T x.

Notation " S ⊆ T " := (subtype_containedIn S T) (at level 70) : subtype.

Definition subtype_notContainedIn {X:UU} (S T : hsubtype X) : hProp := ∃ x:X, S x ∧ ¬ (T x).

Definition subtype_inc {X:UU} {S T : hsubtype X} : S ⊆ T -> S -> T.
Proof.
  intros le s. exact (pr1 s,, le (pr1 s) (pr2 s)).
Defined.

Notation " S ⊈ T " := (subtype_notContainedIn S T) (at level 70) : subtype.

Definition subtype_smallerThan {X:UU} (S T : hsubtype X) : hProp := (S ⊆ T) ∧ (T ⊈ S).

Notation " S ⊊ T " := (subtype_smallerThan S T) (at level 70) : subtype.

Definition subtype_equal {X:UU} (S T : hsubtype X) : hProp := ∀ x, S x ⇔ T x.

Notation " S ≡ T " := (subtype_equal S T) (at level 70) : subtype.

Definition subtype_notEqual {X:UU} (S T : hsubtype X) : hProp := (S ⊈ T) ∨ (T ⊈ S).

Notation " S ≢ T " := (subtype_notEqual S T) (at level 70) : subtype.

Lemma subtype_notEqual_containedIn {X:UU} (S T : hsubtype X) : S ⊆ T -> S ≢ T -> T ⊈ S.
Proof.
  intros ci ne. apply (squash_to_hProp ne); clear ne; intros [n|n].
  - apply (squash_to_hProp n); clear n; intros [x [p q]]. apply fromempty.
    change (neg (T x)) in q. apply q; clear q. apply (ci x). exact p.
  - exact n.
Defined.

Lemma subtype_notEqual_to_negEqual {X:UU} (S T : hsubtype X) : S ≢ T -> ¬ (S ≡ T).
Proof.
  intros n. apply (squash_to_prop n).
  + apply isapropneg.         (* uses funextemptyAxiom *)
  + intros [c|c].
    * apply (squash_to_prop c).
      ** apply isapropneg.         (* uses funextemptyAxiom *)
      ** intros [x [Sx nTx]] e. use nTx; clear nTx. exact (pr1 (e x) Sx).
    * apply (squash_to_prop c).
      ** apply isapropneg.         (* uses funextemptyAxiom *)
      ** intros [x [Tx nSx]] e. use nSx; clear nSx. exact (pr2 (e x) Tx).
Defined.

Lemma subtype_notEqual_from_negEqual {X:UU} (S T : hsubtype X) : LEM -> (S ≢ T <- ¬ (S ≡ T)).
Proof.
  intros lem ne. unfold subtype_equal in ne.
  assert (q := negforall_to_existsneg _ lem ne); clear ne.
  apply (squash_to_hProp q); clear q; intros [x n].
  unfold subtype_notEqual.
  assert (r := weak_fromnegdirprod _ _ n); clear n. unfold dneg in r.
  assert (s := proof_by_contradiction lem r); clear r.
  apply (squash_to_hProp s); clear s. intros s. apply hinhpr. induction s as [s|s].
  + apply ii1, hinhpr. exists x. now apply negimpl_to_conj.
  + apply ii2, hinhpr. exists x. now apply negimpl_to_conj.
Defined.

Definition emptysubtype (X : UU) : hsubtype X
  := λ x, hfalse.

Definition subtype_difference {X:UU} (S T : hsubtype X) : hsubtype X := λ x, S x ∧ ¬ (T x).

Notation " S - T " := (subtype_difference S T) : subtype.

Definition subtype_difference_containedIn {X:UU} (S T : hsubtype X) : (S - T) ⊆ S.
Proof.
  intros x u. exact (pr1 u).
Defined.

Lemma subtype_equal_cond {X:UU} (S T : hsubtype X) : S ⊆ T ∧ T ⊆ S ⇔ S ≡ T.
Proof.
  split.
  - intros c x. induction c as [st ts].
    split.
    + intro s. exact (st x s).
    + intro t. exact (ts x t).
  - intro e. split.
    + intros x s. exact (pr1 (e x) s).
    + intros x t. exact (pr2 (e x) t).
Defined.

Definition subtype_union {X I:UU} (S : I -> hsubtype X) : hsubtype X := λ x, ∃ i, S i x.

Notation "⋃ S" := (subtype_union S) (at level 100, no associativity) : subtype.

Definition carrier_set {X : hSet} (S : hsubtype X) : hSet :=
  make_hSet (carrier S) (isaset_carrier_subset _ S).

Definition subtype_union_containedIn {X:hSet} {I:UU} (S : I -> hsubtype X) i : S i ⊆ ⋃ S
  := λ x s, hinhpr (i,,s).

(** Given a family of subtypes of X indexed by a type I, an element x : X is in
    their intersection if it is an element of each subtype.
 *)

Definition subtype_intersection {X I:UU} (S : I -> hsubtype X) : hsubtype X := λ x, ∀ i, S i x.

Notation "⋂ S" := (subtype_intersection S) (at level 100, no associativity) : subtype.

Theorem hsubtype_univalence {X:UU} (S T : hsubtype X) : (S = T) ≃ (S ≡ T).
Proof.
  intros. intermediate_weq (∏ x, S x = T x).
  - apply weqtoforallpaths.
  - unfold subtype_equal. apply weqonsecfibers; intro x.
    apply weqlogeq.
Defined.

Theorem hsubtype_rect {X:UU} (S T : hsubtype X) (P : S ≡ T -> UU) :
  (∏ e : S=T, P (hsubtype_univalence S T e)) ≃ ∏ f, P f.
Proof.
  intros. apply weqinvweq, weqonsecbase.
Defined.

Ltac hsubtype_induction f e := generalize f; apply hsubtype_rect; intro e; clear f.

Lemma subtype_containment_istrans X : istrans (@subtype_containedIn X).
Proof.
  intros S T U i j x. exact (j x ∘ i x).
Defined.

Lemma subtype_containment_isrefl X : isrefl (@subtype_containedIn X).
Proof.
  intros S x s. exact s.
Defined.

Lemma subtype_containment_ispreorder X : ispreorder (@subtype_containedIn X).
Proof.
  use make_dirprod.
  - apply subtype_containment_istrans.
  - apply subtype_containment_isrefl.
Defined.

Lemma subtype_containment_isantisymm X : isantisymm (@subtype_containedIn X).
Proof.
  intros S T i j. apply (invmap (hsubtype_univalence S T)). apply subtype_equal_cond.
  split; assumption.
Defined.

Lemma subtype_containment_isPartialOrder X : isPartialOrder (@subtype_containedIn X).
Proof.
  use make_dirprod.
  - apply subtype_containment_ispreorder.
  - apply subtype_containment_isantisymm.
Defined.

Lemma subtype_inc_comp {X:UU} {S T U : hsubtype X} (i:S⊆T) (j:T⊆U) (s:S) :
  subtype_inc j (subtype_inc i s) = subtype_inc (λ x, j x ∘ i x) s.
Proof.
  reflexivity.
Defined.

Lemma subtype_deceq {X} (S:hsubtype X) : isdeceq X -> isdeceq (carrier S).
Proof.
  intro i. intros s t. induction (i (pr1 s) (pr1 t)) as [eq|ne].
  - apply ii1, subtypePath_prop, eq.
  - apply ii2. intro eq. apply ne. apply maponpaths. exact eq.
Defined.

Definition isDecidablePredicate {X} (S:X->hProp) := ∏ x, decidable (S x).

Definition subtype_plus {X} (S:hsubtype X) (z:X) : hsubtype X := λ x, S x ∨ z = x.

Definition subtype_plus_incl {X} (S:hsubtype X) (z:X) : S ⊆ subtype_plus S z.
Proof.
  intros s Ss. now apply hinhpr,ii1.
Defined.

Definition subtype_plus_has_point {X} (S:hsubtype X) (z:X) : subtype_plus S z z.
Proof.
  now apply hinhpr, ii2.
Defined.

Definition subtype_plus_in {X} {S:hsubtype X} {z:X} {T:hsubtype X} :
  S ⊆ T -> T z -> subtype_plus S z ⊆ T.
Proof.
  intros le Tz x S'x. apply (squash_to_hProp S'x). intros [Sx|e].
  - exact (le x Sx).
  - induction e. exact Tz.
Defined.

Section Complement.

  Context {X : UU} (S : hsubtype X).

  Definition subtype_complement : hsubtype X := fun x => hneg (S x).

  (** Something can't be in a subset and its complement. *)
  Lemma not_in_subtype_and_complement :
    ∏ x, S x -> subtype_complement x -> empty.
  Proof.
    intros x in_S in_neg_S; exact (in_neg_S in_S).
  Defined.

  (** An intersection containing a set and its complement is empty. *)
  Lemma subtype_complement_intersection_empty {I : UU} {f : I -> hsubtype X} :
    (∑ i : I, f i = S) ->
    (∑ i : I, f i = subtype_complement) ->
    subtype_intersection f ≡ emptysubtype _.
  Proof.
    intros has_S has_neg_S x; use make_dirprod.
    - intros in_intersection.
      pose (in_S := in_intersection (pr1 has_S)).
      pose (in_neg_S := in_intersection (pr1 has_neg_S)).
      cbn in *.

      pose (in_S' := (eqtohomot (pr2 has_S)) x).
      pose (in_neg_S' := (eqtohomot (pr2 has_neg_S)) x).

      apply (not_in_subtype_and_complement x).
      + abstract (induction in_S'; assumption).
      + abstract (induction in_neg_S'; assumption).

    - intros empt; induction empt.
  Qed.

  (** A union containing a set and its complement is the whole set (assuming LEM). *)
  Lemma subtype_complement_union (lem : LEM) {I : UU} {f : I -> hsubtype X} :
    (∑ i : I, f i = S) ->
    (∑ i : I, f i = subtype_complement) ->
    subtype_union f ≡ totalsubtype _.
  Proof.
    intros has_S has_neg_S x; use make_dirprod.
    - intros ?; exact tt.
    - intros ?.
      induction (lem (S x)).
      + apply hinhpr.
        exists (pr1 has_S).
        abstract (rewrite (pr2 has_S); assumption).
      + apply hinhpr.
        exists (pr1 has_neg_S).
        abstract (rewrite (pr2 has_neg_S); assumption).
  Qed.

End Complement.

(* We could define the intersection as follows but this makes it more complicated than it should be *)
Definition binary_intersection' {X : UU} (U V : hsubtype X) : hsubtype X
  := subtype_intersection (λ b,  bool_rect (λ _ : bool, hsubtype X) U V b).

Definition binary_intersection {X : UU} (U V : hsubtype X) : hsubtype X
  := λ x, U x ∧ V x.

Lemma binary_intersection_commutative {X : UU} (U V : hsubtype X)
  : ∏ x : X, (binary_intersection U V) x -> (binary_intersection V U) x.
Proof.
  intros ? p.
  exact (transportf _ (iscomm_hconj (U x) (V x)) p).
Qed.

Definition intersection_contained_l {X : UU} (U V : hsubtype X)
  : subtype_containedIn (binary_intersection U V) U.
Proof.
  intros ? xinUV.
  apply xinUV.
Qed.

Definition intersection_contained_r {X : UU} (U V : hsubtype X)
  : subtype_containedIn (binary_intersection U V) V.
Proof.
  intros ? xinUV.
  apply xinUV.
Qed.

Definition intersection_contained {X : UU} {U U' V V' : hsubtype X}
           (uu : subtype_containedIn U U')
           (vv : subtype_containedIn V V')
  : subtype_containedIn (binary_intersection U V) (binary_intersection U' V').
Proof.
  intros x p.
  cbn.
  split.
  - apply (uu x).
    exact ((intersection_contained_l U V) x p).
  - apply (vv x).
    exact ((intersection_contained_r U V) x p).
Qed.

Lemma isaprop_subtype_containedIn {X : UU} (U V : hsubtype X)
  : isaprop (subtype_containedIn U V).
Proof.
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply V.
Qed.

Definition image_hsubtype {X Y : UU} (U : hsubtype X) (f : X → Y)
  : hsubtype Y := λ y : Y, (∃ x : X, f x = y × U x).

Lemma image_hsubtype_emptyhsubtype {X Y : UU} (f : X → Y)
  : image_hsubtype (emptysubtype X) f = emptysubtype Y.
Proof.
  apply funextsec ; intro y.
  apply hPropUnivalence.
  - intro yinfEmpty.
    use (factor_through_squash _ _ yinfEmpty).
    { apply emptysubtype. }
    intro x.
    apply (pr22 x).
  - intro yinEmpty.
    apply fromempty.
    exact (yinEmpty).
Qed.

Definition image_hsubtype_id {X : UU} (U : hsubtype X)
  : image_hsubtype U (idfun X) = U.
Proof.
  apply funextsec ; intro x.
  apply hPropUnivalence.
  - intro xinIdU.
    use (factor_through_squash _ _ xinIdU).
    { apply U. }
    intro u0.
    assert (p0 : U (pr1 u0) = U x).
    {
      apply maponpaths.
      apply (pr12 u0).
    }
    induction p0.
    apply (pr22 u0).
  - intro xinU.
    apply hinhpr.
    exact (x,, idpath x,, xinU).
Qed.

Definition image_hsubtype_comp {X Y Z : UU} (U : hsubtype X)
           (f : X → Y) (g : Y → Z)
  : image_hsubtype U (funcomp f g) = image_hsubtype (image_hsubtype U f) g.
Proof.
  apply funextsec ; intro z.
  apply hPropUnivalence.
  - intro zinCompU.
    use (factor_through_squash _ _ zinCompU).
    { apply ishinh. }
    intro x.
    apply hinhpr.
    exists (f (pr1 x)).
    exists (pr12 x).
    apply hinhpr.
    exact (pr1 x,, maponpaths f (idpath (pr1 x)),, pr22 x).
  - intro zinCompU.
    use (factor_through_squash _ _ zinCompU).
    { apply ishinh. }
    intro y.
    use (factor_through_squash _ _ (pr22 y)).
    { apply ishinh. }
    intro x.
    apply hinhpr.
    exists (pr1 x).
    split.
    + refine (_ @ (pr12 y)).
      unfold funcomp.
      unfold funcomp.
      apply maponpaths.
      exact (pr12 x).
    + exact (pr22 x).
Qed.

Definition hsubtype_preserving {X Y : UU} (U : hsubtype X) (V : hsubtype Y) (f : X → Y)
  : UU := subtype_containedIn (image_hsubtype U f) V.

Lemma isaprop_hsubtype_preserving {X Y : UU} (U : hsubtype X) (V : hsubtype Y) (f : X → Y)
  : isaprop (hsubtype_preserving U V f).
Proof.
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply V.
Qed.

Lemma id_hsubtype_preserving {X : UU} (U : hsubtype X) : hsubtype_preserving U U (idfun X).
Proof.
  intros x xinU.
  rewrite image_hsubtype_id in xinU.
  exact xinU.
Qed.

Lemma comp_hsubtype_preserving {X Y Z : UU}
      {U : hsubtype X} {V : hsubtype Y} {W : hsubtype Z}
      {f : X → Y} {g : Y → Z}
      (fsp : hsubtype_preserving U V f) (gsp : hsubtype_preserving V W g)
  : hsubtype_preserving U W (funcomp f g).
Proof.
  intros z zinU.
  rewrite image_hsubtype_comp in zinU.
  apply (gsp _).
  unfold image_hsubtype.
  use (factor_through_squash _ _ zinU).
  { apply ishinh. }
  intro y.
  apply hinhpr.
  exists (pr1 y).
  exists (pr12 y).
  apply (fsp _).
  exact (pr22 y).
Qed.

Lemma empty_hsubtype_preserving {X Y : UU} (f : X → Y)
  : hsubtype_preserving (emptysubtype X) (emptysubtype Y) f.
Proof.
  unfold hsubtype_preserving.
  rewrite image_hsubtype_emptyhsubtype.
  apply subtype_containment_isrefl.
Qed.

Lemma total_hsubtype_preserving {X Y : UU} (f : X → Y)
  : hsubtype_preserving (totalsubtype X) (totalsubtype Y) f.
Proof.
  exact (λ _ _, tt).
Qed.

Section singletons.
  Definition singleton {X : UU} (x : X) : hsubtype X
    := λ (a : X), ∥ a = x ∥.

  (* The canonical element of the singleton subtype. *)
  Definition singleton_point {X : UU} {x : X} : singleton x
    := (x ,, hinhpr (idpath x)).

  Definition iscontr_singleton {X : hSet} (x : X) : iscontr (singleton x).
  Proof.
    use make_iscontr.
    - exact singleton_point.
    - intros t.
      apply subtypePath_prop.
      apply(squash_to_prop (pr2 t)).
      apply setproperty.
      intro ; assumption.
  Defined.

  Definition singleton_is_in {X : UU} (A : hsubtype X) (a : A)
    : (singleton (pr1 a)) ⊆ A.
  Proof.
    intro y.
    use hinhuniv.
    exact(λ (p : y = (pr1 a)), transportb A p (pr2 a)).
  Defined.
End singletons.
