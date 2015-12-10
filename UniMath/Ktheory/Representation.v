Require Import
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.Bifunctor.
Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.opp_precat
        UniMath.CategoryTheory.yoneda
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset.
Set Automatic Introduction.
Local Open Scope cat.

Definition Universal {C:Precategory} (X:[C^op,SET]) (c:C)
  := Σ (x:c ⇒ X), ∀ (c':C), isweq (λ f : c' → c, x ⟲ f).

Lemma iso_Universal_weq {C:Precategory} {X Y:[C^op,SET]} (c:C) :
  iso X Y -> Universal X c ≃ Universal Y c.
Proof.
  intro i.
  set (I := (functor_iso_pointwise_if_iso
             C^op SET (homset_property SET) X Y (pr1 i) (pr2 i))).
  refine (weqbandf _ _ _ _).
  - apply hset_iso_equiv_weq. unfold arrow, functor_object_application. exact (I c).
  - simpl; intros x. apply weqonsecfibers; intro b. apply weqiff.
    + refine (twooutof3c_iff_1_homot _ _ _ _ _).
      * exact (pr1 i ◽ opp_ob b).
      * intro f; unfold funcomp; simpl.
        exact (apevalat x (nat_trans_ax (pr1 i) _ _ f)).
      * exact (hset_iso_is_equiv _ _ (I b)).
    + apply isapropisweq.
    + apply isapropisweq.
Defined.

Definition Representation {C:Precategory} (X:[C^op,SET]) : UU
  := Σ (c:C), Universal X c.

Definition isRepresentable {C:Precategory} (X:[C^op,SET]) := ∥ Representation X ∥.

Lemma isaprop_Representation {C:category} (X:[C^op,SET]) :
  isaprop (@Representation C X).
Proof.

Abort.

Definition iso_Representation_weq {C:Precategory} (X Y:[C^op,SET]) :
  nat_iso X Y -> Representation X ≃ Representation Y.
Proof.
  intros i. apply weqfibtototal; intro c. apply iso_Universal_weq; assumption.
Defined.

(* categories of functors with representations *)

Definition RepresentedFunctor (C:Precategory) : Precategory
  := categoryWithStructure [C^op,SET] Representation.

Definition toRepresentation {C:Precategory} (X : RepresentedFunctor C) :
  Representation (pr1 X)
  := pr2 X.

Definition RepresentableFunctor (C:Precategory) : Precategory
  := categoryWithStructure [C^op,SET] isRepresentable.

Definition toRepresentableFunctor {C:Precategory} :
  RepresentedFunctor C ==> RepresentableFunctor C :=
  functorWithStructures (λ c, hinhpr).

(* make a representation of a functor *)

Definition makeRepresentation {C:Precategory} {c:C} {X:[C^op,SET]} (x:c ⇒ X) :
  (∀ (c':C), bijective (λ f : c' → c, x ⟲ f)) -> Representation X.
Proof.
  intros bij. exists c. exists x. intros c'. apply set_bijection_to_weq.
  - exact (bij c').
  - apply setproperty.
Defined.

(* universal aspects of represented functors *)

Definition universalObject {C:Precategory} {X:[C^op,SET]} (r:Representation X) : C
  := pr1 r.

Definition universalElement {C:Precategory} {X:[C^op,SET]} (r:Representation X) :
  universalObject r ⇒ X
  := pr1 (pr2 r).

Coercion universalElement : Representation >-> pr1hSet.

Definition universalProperty {C:Precategory} {X:[C^op,SET]} (r:Representation X) (c:C) :
  c → universalObject r ≃ c ⇒ X
  := weqpair (λ f : c → universalObject r, r ⟲ f)
             (pr2 (pr2 r) c).

Definition universalMap {C:Precategory} {X:[C^op,SET]} (r:Representation X) {c:C} :
  c ⇒ X -> c → universalObject r
  := invmap (universalProperty _ _).

Notation "r \\ x" := (universalMap r x) (at level 50, left associativity) : cat.

Definition universalMap' {C:Precategory} {X:[C^op^op,SET]} (r:Representation X) {c:C} :
  X ⇐ c -> c ← universalObject r
  := invmap (universalProperty _ _).

Notation "x // r" := (universalMap' r x) (at level 50, left associativity) : cat.

Definition universalMapProperty {C:Precategory} {X:[C^op,SET]} (r:Representation X)
      {c:C} (x : c ⇒ X) :
  r ⟲ (r \\ x) = x
  := homotweqinvweq (universalProperty r c) x.

Definition mapUniqueness {C:Precategory} (X:[C^op,SET]) (r : Representation X) (c:C)
           (f g: c → universalObject r) :
  r ⟲ f = r ⟲ g -> f = g
  := invmaponpathsweq (universalProperty _ _) _ _.

Definition universalMapUniqueness {C:Precategory} {X:[C^op,SET]} {r:Representation X}
      {c:C} (x : c ⇒ X) (f : c → universalObject r) :
  r ⟲ f = x -> f = r \\ x
  := pathsweq1 (universalProperty r c) f x.

Definition universalMapIdentity {C:Precategory} {X:[C^op,SET]} (r:Representation X) :
  r \\ r = identity _.
Proof. apply pathsinv0. apply universalMapUniqueness. apply arrow_mor_id. Qed.

Definition universalMapUniqueness' {C:Precategory} {X:[C^op,SET]} {r:Representation X}
      {c:C} (x : c ⇒ X) (f : c → universalObject r) :
  f = r \\ x -> r ⟲ f = x
  := pathsweq1' (universalProperty r c) f x.

Lemma univ_arrow_mor_assoc {C:Precategory} {a b:C} {Z:[C^op,SET]}
      (f : a → b) (z : b ⇒ Z) (t : Representation Z) :
  (t \\ z) ∘ f = t \\ (z ⟲ f).
Proof.
  apply universalMapUniqueness.
  refine (arrow_mor_mor_assoc _ _ _ @ _).
  apply maponpaths.
  apply universalMapProperty.
Qed.

(*  *)

Lemma uOF_identity {C:Precategory} {X:[C^op,SET]} (r:Representation X) :
  r \\ (identity X ⟳ r) = identity _.
Proof.
  unfold nat_trans_id; simpl.
  refine (transportb (λ k, _ \\ k = _) (identityFunction' _ _) _).
  apply universalMapIdentity.
Qed.

Lemma uOF_comp {C:Precategory} {X Y Z:[C^op,SET]}
      (r:Representation X)
      (s:Representation Y)
      (t:Representation Z)
      (p:X→Y) (q:Y→Z) :
    t \\ ((q ∘ p) ⟳ r) = (t \\ (q ⟳ s)) ∘ (s \\ (p ⟳ r)).
Proof.
  refine (transportf (λ k, _ \\ k = _) (nattrans_nattrans_arrow_assoc _ _ _) _).
  refine (_ @ !univ_arrow_mor_assoc _ _ _).
  apply maponpaths.
  refine (_ @ nattrans_arrow_mor_assoc _ _ _).
  apply (maponpaths (λ k, q ⟳ k)).
  apply pathsinv0.
  apply universalMapProperty.
Qed.

Definition universalObjectFunctor (C:Precategory) : RepresentedFunctor C ==> C.
Proof.
  refine (makeFunctor _ _ _ _).
  - intro X. exact (universalObject (pr2 X)).
  - intros X Y p; simpl. exact (pr2 Y \\ (p ⟳ pr2 X)).
  - intros X; simpl. apply uOF_identity.
  - intros X Y Z p q; simpl. apply uOF_comp.
Defined.

(* move upstream *)
Definition comp_func_on_mor {A B C:Precategory} (F:[A,B]) (G:[B,C]) {a a':A} (f:a→a') :
  G □ F ▭ f = G ▭ (F ▭ f).
Proof. reflexivity. Defined.

Definition universalObjectFunctor_on_map (C:Precategory) {X Y:RepresentedFunctor C} (p:X→Y) :
  universalObjectFunctor C ▭ p = pr2 Y \\ (p ⟳ pr2 X).
Proof. reflexivity. Defined.

Lemma universalObjectFunctor_comm (C:Precategory) {X Y:RepresentedFunctor C} (p:X→Y) :
  p ⟳ universalElement (pr2 X) = universalElement (pr2 Y) ⟲ universalObjectFunctor C ▭ p.
Proof.
  change (universalObjectFunctor C ▭ p) with (pr2 Y \\ (p ⟳ pr2 X)).
  apply pathsinv0, universalMapProperty.
Defined.

Definition embeddingRepresentability {C D:Precategory}
           {i:C==>D} (emb:fully_faithful i) {Y:D^op==>SET} (s:Representation Y) :
           (Σ c, universalObject s = i c) -> Representation (Y □ functor_opp i).
Proof.
  intros ce. exists (pr1 ce).
  exists (transportf (λ d, Y d : hSet) (pr2 ce) s).
  intro c'. apply (twooutof3c (# i) (λ g, _ ⟲ g)).
  - apply emb.
  - induction (pr2 ce). exact (weqproperty (universalProperty _ _)).
Defined.

(*** Some standard functors to consider representing *)

(** the functor represented by an object *)

Definition Hom1 {C:Precategory} (c:C) : [C^op,SET].
Proof.
  refine (makeFunctor_op _ _ _ _).
  - intro b. exact (Hom C b c).
  - intros b a f g; simpl. exact (g ∘ f).
  - abstract (intros b; simpl; apply funextsec; intro g; apply id_left) using L.
  - abstract (intros i j k f g; simpl; apply funextsec; intro h;
              rewrite <- assoc; reflexivity) using L.
Defined.

Lemma Hom1_Representation {C:Precategory} (c:C) : Representation (Hom1 c).
Proof.
  exists c. exists (identity c). intro b. apply (isweqhomot (idweq _)).
  - abstract (intro f; unfold arrow_morphism_composition; unfold Hom1, idfun; simpl;
              apply pathsinv0, id_right) using R.
  - abstract (apply weqproperty) using T.
Defined.

(** maps from Hom1 to functors *)

Lemma compose_SET {X Y Z:SET} (f:X→Y) (g:Y→Z) : g∘f = λ x, g(f x).
Proof. reflexivity. Defined.

Definition element_to_nattrans {C:Precategory} (X:[C^op,SET]) (c:C) :
  c ⇒ X -> Hom1 c → X.
Proof.
  intros x. refine (makeNattrans_op _ _).
  - unfold Hom1; simpl; intros b f. exact (x ⟲ f).
  - abstract (intros a b f; apply funextsec; intro g; apply arrow_mor_mor_assoc) using L.
Defined.

(** representable functors are isomorphic to one represented by an object  *)

Theorem Representation_to_iso {C:Precategory} (X:[C^op,SET]) (r:Representation X) :
  iso (Hom1 (universalObject r)) X.
Proof.
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ (element_to_nattrans X (universalObject r) (universalElement r))).
  intro b. apply (pr2 (weq_iff_iso_SET _)). exact (pr2 (pr2 r) b).
Defined.

(** initial and final objects and zero maps  *)

Definition UnitFunctor (C:Precategory) : C ==> SET.
  refine (_,,_).
  { exists (λ c, unitset). exact (λ a b f t, t). }
  { split.
    { intros a. reflexivity. }
    { intros a b c f g. reflexivity. } }
Defined.

Definition TerminalObject (C:Precategory) := Representation (UnitFunctor C^op).

Definition terminalObject {C} (t:TerminalObject C) : ob C := universalObject t.

Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) :
  Hom C c (terminalObject t)
  := t \\ tt.

Definition InitialObject (C:Precategory) := TerminalObject C^op.

Definition initialObject {C} (i:InitialObject C) : ob C := universalObject i.

Definition initialArrow {C} (i:InitialObject C) (c:ob C) :
  Hom C (initialObject i) c
  := rm_opp_mor (tt // i).

Definition init_to_opp {C:Precategory} : InitialObject C -> TerminalObject C^op
  := λ i, i.

Definition term_to_opp {C:Precategory} : TerminalObject C -> InitialObject C^op.
Proof. intros. unfold InitialObject. now induction (opp_opp_precat C). Defined.

(** zero objects, as an alternative to ZeroObject.v *)

Definition ZeroObject (C:Precategory)
  := Σ z:ob C, Universal (UnitFunctor C^op) z × Universal (UnitFunctor C^op^op) z.

Definition zero_to_terminal (C:Precategory) : ZeroObject C -> TerminalObject C
  := λ z, pr1 z ,, pr1 (pr2 z).

Definition zero_to_initial (C:Precategory) : ZeroObject C -> InitialObject C
  := λ z, pr1 z ,, pr2 (pr2 z).

Definition zero_opp (C:Precategory) : ZeroObject C -> ZeroObject C^op.
Proof.
  intro z. induction z as [z k]. exists z.
  induction (opp_opp_precat C).
  exact (pr2 k,,pr1 k).
Defined.

Definition hasZeroObject (C:Precategory) := ∥ ZeroObject C ∥.

Definition haszero_opp (C:Precategory) : hasZeroObject C -> hasZeroObject C^op
  := hinhfun (zero_opp C).

Definition zeroMap' (C:Precategory) (a b:ob C) (o:ZeroObject C) : Hom C a b
  := (zero_to_initial C o \\ tt) ∘ (zero_to_terminal C o \\ tt).

Lemma zero_eq_zero_opp (C:Precategory) (a b:ob C) (o:ZeroObject C) :
  zeroMap' C^op (opp_ob b) (opp_ob a) (zero_opp C o)
  =
  opp_mor (zeroMap' C a b o).
Proof.
  intros.
  try reflexivity.


Abort.

(** binary products and coproducts *)

Definition HomPair {C:Precategory} (a b:C) : C^op ==> SET.
Proof.
  refine (makeFunctor_op _ _ _ _).
  - intro c. exact (Hom C c a × Hom C c b) % set.
  - simpl. intros c d f x. exact (pr1 x ∘ f ,, pr2 x ∘ f).
  - abstract (simpl; intro c; apply funextsec; intro x;
              apply dirprod_eq; apply id_left) using B.
  - abstract (simpl; intros c d e f g;
              apply funextsec; intro x;
              apply dirprod_eq; apply pathsinv0, assoc) using C.
Defined.

Definition BinaryProduct {C:Precategory} (a b:C) :=
  Representation (HomPair a b).

Definition pr_1 {C:Precategory} {a b:C} (prod : BinaryProduct a b) :
  universalObject prod → a
  := pr1 (universalElement prod).

Definition pr_2 {C:Precategory} {a b:C} (prod : BinaryProduct a b) :
  universalObject prod → b
  := pr2 (universalElement prod).

Definition binaryProductMap {C:Precategory} {a b:C} (prod : BinaryProduct a b)
           {c:C} : c → a -> c → b -> c → universalObject prod
  := λ f g, prod \\ (f,,g).

Lemma binaryProductMapUniqueness {C:Precategory} {a b:C} (prod : BinaryProduct a b)
      {c:C} (f g : Hom C c (universalObject prod)) :
  pr_1 prod ∘ f = pr_1 prod ∘ g ->
  pr_2 prod ∘ f = pr_2 prod ∘ g -> f = g.
Proof. intros r s. apply mapUniqueness. apply dirprod_eq.
       exact r. exact s.
Defined.

Definition BinarySum {C:Precategory} (a b:C) :=
  BinaryProduct (opp_ob a) (opp_ob b).

Definition in_1 {C:Precategory} {a b:C} (sum : BinarySum a b) :
  Hom C a (universalObject sum)
  := pr_1 sum.

Definition in_2 {C:Precategory} {a b:C} (sum : BinarySum a b) :
  Hom C b (universalObject sum)
  := pr_2 sum.

Definition binarySumMap {C:Precategory} {a b:C} (sum : BinarySum a b)
           {c:C} : a → c -> b → c -> rm_opp_ob (universalObject sum) → c
  := λ f g, rm_opp_mor (sum \\ (opp_mor f,,opp_mor g)).

Lemma binarySumMapUniqueness {C:Precategory} {a b:C} (sum : BinarySum a b)
      {c:C} (f g : Hom C (rm_opp_ob (universalObject sum)) c) :
  f ∘ in_1 sum = g ∘ in_1 sum ->
  f ∘ in_2 sum = g ∘ in_2 sum -> f = g.
Proof. intros r s. apply opp_mor_eq, mapUniqueness, dirprod_eq; assumption. Defined.

(** products and coproducts *)

Definition HomFamily (C:Precategory) {I} (c:I -> ob C) : C^op ==> SET.
Proof.
  refine (_,,_).
  - refine (_,,_).
    + intros x. exact (∀ i, Hom C x (c i)) % set.
    + intros x y f p i; simpl; simpl in p.
      exact (compose (C:=C) f (p i)).
  - abstract (split;
    [ intros a; apply funextsec; intros f; apply funextsec; intros i; simpl;
      apply id_left
    | intros x y z p q;
      apply funextsec; intros f; apply funextsec; intros i; simpl;
      apply pathsinv0, assoc]) using L.
Defined.

Definition Product {C:Precategory} {I} (c:I -> ob C)
  := Representation (HomFamily C c).

Definition pr_ {C:Precategory} {I} {c:I -> ob C} (prod : Product c) (i:I) :
  universalObject prod → c i
  := universalElement prod i.

Definition productMapExistence {C:Precategory} {I} {c:I -> ob C} (prod : Product c)
      {a:C} :
  (∀ i, Hom C a (c i)) -> Hom C a (universalObject prod)
  := λ f, prod \\ f.

Lemma productMapUniqueness {C:Precategory} {I} {c:I -> ob C} (prod : Product c)
      {a:C} (f g : Hom C a (universalObject prod)) :
  (∀ i, pr_ prod i ∘ f = pr_ prod i ∘ g) -> f = g.
Proof.
  intro e. apply mapUniqueness. apply funextsec; intro i. apply e.
Defined.

Definition Sum {C:Precategory} {I} (c:I -> ob C)
  := Representation (HomFamily C^op c).

Definition in_ {C:Precategory} {I} {c:I -> ob C} (sum : Sum c) (i:I) :
  c i → universalObject sum
  := rm_opp_mor (universalElement sum i).

Definition sumMapExistence {C:Precategory} {I} {c:I -> ob C} (sum : Sum c)
      {a:C} :
  (∀ i, Hom C (c i) a) -> Hom C (universalObject sum) a
  := λ f, f // sum.

Lemma sumMapUniqueness {C:Precategory} {I} {c:I -> ob C} (sum : Sum c)
      {a:C} (f g : Hom C (universalObject sum) a) :
  (∀ i, f ∘ in_ sum i = g ∘ in_ sum i) -> f = g.
Proof.
  intro e. apply opp_mor_eq, mapUniqueness. apply funextsec; intro i. apply e.
Defined.

(** equalizers and coequalizers *)

Local Open Scope cat'.

Definition Equalization {C:Precategory} {c d:C} (f g:c→d) :
  C^op ==> SET.
Proof.
  refine (makeFunctor_op _ _ _ _).
  - intro b. refine (_,,_).
    + exact (Σ p:b → c, f∘p = g∘p).
    + abstract (apply isaset_total2;
      [ apply homset_property
      | intro; apply isasetaprop; apply homset_property]) using L.
  - intros b a e w; simpl in *. exists (pr1 w ∘ e).
    abstract (rewrite <- 2? assoc; apply maponpaths; exact (pr2 w)) using M.
  - abstract (
        intros b; apply funextsec; intro w; apply subtypeEquality;
        [ intro; apply homset_property
        | simpl; apply id_left]) using N.
  - abstract (
        intros a'' a' a r s; apply funextsec;
        intro w; apply subtypeEquality;
        [ intro; apply homset_property
        | apply pathsinv0, assoc ]) using O.
Defined.

Definition Equalizer {C:Precategory} {c d:C} (f g:c→d) :=
  Representation (Equalization f g).

Definition equalizerMap {C:Precategory} {c d:C} {f g:c→d} (eq : Equalizer f g) :
  universalObject eq → c
  := pr1 (universalElement eq).

Definition equalizerEquation {C:Precategory} {c d:C} {f g:c→d} (eq : Equalizer f g) :
  f ∘ equalizerMap eq = g ∘ equalizerMap eq
  := pr2 (universalElement eq).

Definition Coequalizer {C:Precategory} {c d:C} (f g:c→d) :=
  Representation (Equalization (opp_mor f) (opp_mor g)).

Definition coequalizerMap {C:Precategory} {c d:C} {f g:c→d} (coeq : Coequalizer f g) :
  d → universalObject coeq
  := pr1 (universalElement coeq).

Definition coequalizerEquation {C:Precategory} {c d:C} {f g:c→d} (coeq : Coequalizer f g) :
  coequalizerMap coeq ∘ f = coequalizerMap coeq ∘ g
  := pr2 (universalElement coeq).

(** pullbacks and pushouts  *)

Definition PullbackCone {C:Precategory} {a b c:C} (f:a→c) (g:b→c) :
  C^op ==> SET.
Proof.
  intros.
  refine (makeFunctor_op _ _ _ _).
  - intros t. refine (_,,_).
    + exact (Σ (p: t → a × t → b), f ∘ pr1 p = g ∘ pr2 p).
    + abstract (apply isaset_total2;
      [ apply isasetdirprod; apply homset_property
      | intro; apply isasetaprop; apply homset_property]) using L.
  - intros t u p w; simpl in *.
    exists (pr1 (pr1 w) ∘ p,, pr2 (pr1 w) ∘ p).
    abstract (
        simpl; rewrite <- 2? assoc; apply maponpaths; exact (pr2 w)) using M.
  - abstract (intros t; simpl; apply funextsec; intro w;
              induction w as [w eq]; induction w as [p q];
              simpl in *; refine (total2_paths2 _ _);
              [ rewrite 2? id_left; reflexivity
              | apply proofirrelevance; apply homset_property]) using N.
  - abstract (
        intros r s t p q; simpl in *; apply funextsec; intro w;
        refine (total2_paths2 _ _);
        [ simpl; rewrite 2? assoc; reflexivity
        | apply proofirrelevance; apply homset_property]) using P.
Defined.

Definition Pullback {C:Precategory} {a b c:C} (f:a→c) (g:b→c) :=
  Representation (PullbackCone f g).

Definition pb_1 {C:Precategory} {a b c:C} {f:a→c} {g:b→c} (pb : Pullback f g) :
  universalObject pb → a
  := pr1 (pr1 (universalElement pb)).

Definition pb_2 {C:Precategory} {a b c:C} {f:a→c} {g:b→c} (pb : Pullback f g) :
  universalObject pb → b
  := pr2 (pr1 (universalElement pb)).

Definition pb_eqn {C:Precategory} {a b c:C} {f:a→c} {g:b→c} (pb : Pullback f g) :
  f ∘ pb_1 pb = g ∘ pb_2 pb
  := pr2 (universalElement pb).

Definition Pushout {C:Precategory} {a b c:C} (f:a→b) (g:a→c) :=
  Representation (PullbackCone (opp_mor f) (opp_mor g)).

Definition po_1 {C:Precategory} {a b c:C} {f:a→b} {g:a→c} (po : Pushout f g) :
  b → universalObject po
  := pr1 (pr1 (universalElement po)).

Definition po_2 {C:Precategory} {a b c:C} {f:a→b} {g:a→c} (po : Pushout f g) :
  c → universalObject po
  := pr2 (pr1 (universalElement po)).

Definition po_eqn {C:Precategory} {a b c:C} {f:a→c} {g:a→c} (po : Pushout f g) :
  po_1 po ∘ f = po_2 po ∘ g
  := pr2 (universalElement po).

(** kernels and cokernels *)

Local Open Scope cat'.

Definition Annihilator (C:Precategory) (zero:hasZeroMaps C) {c d:C} (f:c → d) :
  C^op ==> SET.
Proof.
  refine (_,,_).
  { refine (_,,_).
    { intro b. exists (Σ g:Hom C b c, f ∘ g = pr1 zero b d).
      abstract (apply isaset_total2; [ apply setproperty |
      intro g; apply isasetaprop; apply homset_property ]) using L. }
    { intros a b p ge; simpl.
      exists (pr1 ge ∘ opp_mor p).
      { abstract (
            refine (! assoc _ _ _ @ _); rewrite (pr2 ge);
            apply (pr2 (pr2 zero) _ _ _ _)) using M. } } }
  { abstract (split;
    [ intros x; apply funextsec; intros [r rf0];
      apply subtypeEquality;
      [ intro; apply homset_property
      | simpl; unfold opp_mor; apply id_left ]
    | intros w x y t u; apply funextsec; intros [r rf0];
      apply subtypeEquality;
      [ intro; apply homset_property
      | simpl; unfold opp_mor; apply pathsinv0, assoc ] ]) using N. }
Defined.

Definition Kernel {C:Precategory} (zero:hasZeroMaps C) {c d:ob C} (f:c → d) :=
  Representation (Annihilator C zero f).

Definition Cokernel {C:Precategory} (zero:hasZeroMaps C) {c d:ob C} (f:c → d) :=
  Representation (Annihilator C^op (hasZeroMaps_opp C zero) f).

Definition kernelMap {C:Precategory} {zero:hasZeroMaps C} {c d:ob C} {f:c → d}
           (r : Kernel zero f) : universalObject r → c
  := pr1 (universalElement r).

Definition kernelEquation {C:Precategory} {zero:hasZeroMaps C} {c d:ob C} {f:c → d}
           (ker : Kernel zero f) :
  f ∘ kernelMap ker = pr1 zero _ _
  := pr2 (universalElement ker).

Definition cokernelMap {C:Precategory} {zero:hasZeroMaps C} {c d:ob C} {f:c → d}
           (r : Cokernel zero f) : d → universalObject r
  := pr1 (universalElement r).

Definition cokernelEquation {C:Precategory} {zero:hasZeroMaps C} {c d:ob C} {f:c → d}
           (coker : Cokernel zero f) :
  cokernelMap coker ∘ f = pr1 zero _ _
  := pr2 (universalElement coker).

(** fibers of maps between functors *)

Definition fiber {C:Precategory} {X Y:[C^op,SET]} (p : X → Y) {c:C} (y : c ⇒ Y) :
  C^op ==> SET.
Proof.
  refine (makeFunctor_op _ _ _ _).
  - intro b.
    exists (Σ fx : (b → c) × (b ⇒ X), p ⟳ pr2 fx = y ⟲ pr1 fx).
    abstract (apply isaset_total2;
        [ apply isaset_dirprod, setproperty; apply homset_property
        | intros [f x]; apply isasetaprop; apply setproperty ]) using K.
  - simpl; intros b b' g fxe.
    exists (pr1 (pr1 fxe) ∘ g,, pr2 (pr1 fxe) ⟲ g).
    abstract (simpl; rewrite nattrans_arrow_mor_assoc, arrow_mor_mor_assoc;
              apply maponpaths; exact (pr2 fxe)) using M.
  - abstract (intro b; apply funextsec; intro w;
              induction w as [w e]; induction w as [f x]; simpl;
              refine (total2_paths2 _ _);
              [ apply dirprod_eq; [ apply id_left | apply arrow_mor_id ]
              | apply setproperty]) using R.
  - abstract (intros b b' b'' g g''; apply funextsec; intro w;
              induction w as [w e]; induction w as [f x]; simpl;
              refine (total2_paths2 _ _);
              [ apply dirprod_eq;
                [ apply pathsinv0, assoc | apply arrow_mor_mor_assoc ]
              | apply setproperty ]) using T.
Defined.

(* this is representability of a map between two functors, in the sense of
   Grothendieck.  See EGA Chapter 0. *)

Definition Representation_Map {C:Precategory} {X Y:[C^op,SET]} (p : X → Y) :=
  ∀ (c : C) (y : c ⇒ Y), Representation (fiber p y).

Definition isRepresentable_Map {C:Precategory} {X Y:[C^op,SET]} (p : X → Y) :=
  ∀ (c : C) (y : c ⇒ Y), isRepresentable (fiber p y).

(** limits and colimits  *)

Definition cone {I C:Precategory} (c:C) (D: [I,C]) : UU
  := Σ (φ : ∀ i, Hom C c (D ◾ i)),
     ∀ i j (e : i → j), D ▭ e ∘ φ i = φ j.

Lemma cone_eq {C I:Precategory} (c:C^op) (D: I==>C) (p q:cone (C:=C) c D) :
  pr1 p ~ pr1 q -> p = q.
Proof.
  intros h. apply subtypeEquality.
  { intro r.
    apply impred_isaprop; intro i;
    apply impred_isaprop; intro j;
    apply impred_isaprop; intro e.
    apply homset_property. }
  apply funextsec; intro i; apply h.
Qed.

Definition cone_functor {I C:Precategory} : [I,C] ==> [C^op,SET].
Proof.
  intros.
  refine (_,,_).
  { refine (_,,_).
    { intros D. refine (_,,_).
      { refine (_,,_).
        - intro c. exists (cone (C:=C) c D).
          abstract (
              apply isaset_total2;
              [ apply impred_isaset; intro i; apply homset_property
              | intros φ;
                apply impred_isaset; intro i;
                apply impred_isaset; intro j;
                apply impred_isaset; intro e; apply isasetaprop;
                apply homset_property]) using LLL.
        - simpl; intros a b f φ.
          exists (λ i, pr1 φ i ∘ f).
          abstract (
              intros i j e; simpl;
              rewrite <- assoc;
              apply maponpaths;
              apply (pr2 φ)) using M. }
      { abstract (split;
        [ intro c; simpl;
          apply funextsec; intro p;
          apply cone_eq;
          intro i; simpl;
          apply id_left
        | intros a b c f g; simpl; apply funextsec; intro p;
          apply cone_eq; simpl; intro i; apply pathsinv0, assoc ]) using N. } }
    { intros D D' f; simpl.
      refine (_,,_).
      - simpl. unfold cone. intros c φ.
        refine (_,,_).
        + intros i. exact (pr1 f i ∘ pr1 φ i).
        + abstract (
              simpl; intros i j e; assert (L := pr2 φ i j e); simpl in L;
              rewrite <- L; rewrite <- assoc; rewrite <- assoc;
              apply maponpaths; apply pathsinv0; apply nat_trans_ax) using P.
      - abstract (intros a b g; simpl;
                  apply funextsec; intro p; apply cone_eq; intro i; simpl;
                  apply pathsinv0, assoc) using Q. } }
  { abstract ( unfold cone; split;
    [ intros D; simpl;
      refine (total2_paths2 _ _);
      [ apply funextsec; intro c;
        apply funextsec; intro φ; simpl;
        refine (total2_paths _ _);
        [ simpl; apply funextsec; intro i; apply id_right
        | apply funextsec; intro i;
          apply funextsec; intro j;
          apply funextsec; intro e;
          apply homset_property ]
      | apply isaprop_is_nat_trans; exact (homset_property SET)]
    | intros D D' D'' p q;
      simpl;
      refine (total2_paths2 _ _);
      [ apply funextsec; intro c; simpl; apply funextsec; intro φ;
        refine (total2_paths2 _ _);
        [ simpl; apply funextsec; intro i; apply assoc
        | apply funextsec; intro i;
          apply funextsec; intro j;
          apply funextsec; intro e;
          apply homset_property ]
      | apply isaprop_is_nat_trans; exact (homset_property SET)] ]) using R. }
Defined.

Definition cocone_functor {I C:Precategory} : [I,C]^op ==> [C^op^op,SET]
  := cone_functor □ op_move op_functor.

Definition Limit {C I:Precategory} (D: I==>C) := Representation (cone_functor D).

Definition Colimit {C I:Precategory} (D: I==>C) := Representation (cocone_functor D).

Definition proj_ {C I:Precategory} {D: I==>C} (lim:Limit D) (i:I) : universalObject lim → D i.
Proof. intros. exact ((pr1 (universalElement lim) i)). Defined.

Definition inj_ {C I:Precategory} {D: I==>C} (colim:Colimit D) (i:I) : D i → universalObject colim.
Proof. intros. exact ((pr1 (universalElement colim) i)). Defined.

Definition proj_comm {C I:Precategory} {D: I==>C} (lim:Limit D) {i j:I} (f:i→j) :
  # D f ∘ proj_ lim i = proj_ lim j.
Proof. intros. exact (pr2 (universalElement lim) _ _ f). Defined.

Definition inj_comm {C I:Precategory} {D: I==>C} (colim:Colimit D) {i j:I} (f:i→j) :
  inj_ colim j ∘ # D f = inj_ colim i.
Proof. intros. exact (pr2 (universalElement colim) _ _ f). Defined.

Definition hasLimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Limit D.

Definition hasColimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Colimit D.

Definition lim_functor (C:Precategory) (lim:hasLimits C) (I:Precategory) :
  [I,C] ==> C
  := universalObjectFunctor C □ addStructure cone_functor (lim I).

Definition colim_functor (C:Precategory) (colim:hasColimits C) (I:Precategory) :
  [I,C] ==> C
  := functor_rm_op (
         universalObjectFunctor C^op □ addStructure cocone_functor (colim I)).

Lemma bifunctor_assoc_repn {B C:Precategory} (X : [B, [C^op,SET]]) :
  (∀ b, Representation (X ◾ b)) -> Representation (bifunctor_assoc X).
Proof.
  intro r. set (X' := addStructure X r).
  change (categoryWithStructure [C ^op, SET] Representation) with (RepresentedFunctor C) in X'.
  set (F := universalObjectFunctor C □ X').
  exists F. refine (_,,_).
  { refine (_,,_).
    { intro b. exact (universalElement (r b)). }
    { abstract (intros b b' f; exact (!universalObjectFunctor_comm C (X' ▭ f))) using K. } }
  { intro F'. apply bijection_to_weq.
    split.
    { intro x'. unfold arrow in x'.
      refine (_,,_).
      { refine (makeNattrans _ _).
        { intro b. exact (r b \\ pr1 x' b). }
        { abstract (intros b b' f; simpl;
                    refine (univ_arrow_mor_assoc (F' ▭ f) (pr1 x' b') (r b') @ _);
                    intermediate_path (r b' \\ (X ▭ f ⟳ pr1 x' b));
                    [ apply maponpaths, (pr2 x' b b' f)
                    | unfold F;
                      rewrite comp_func_on_mor;
                      rewrite (universalObjectFunctor_on_map C (X' ▭ f));
                      change (pr2 (X' ◾ b')) with (r b');
                      change (pr2 (X' ◾ b)) with (r b);
                      change (X' ▭ f) with (X ▭ f);
                      refine (_ @ !univ_arrow_mor_assoc _ _ _);
                      apply maponpaths;
                      rewrite <- nattrans_arrow_mor_assoc;
                      apply (maponpaths (λ k, X ▭ f ⟳ k));
                      apply pathsinv0;
                      exact (universalMapProperty (r b) (pr1 x' b)) ]) using R. } }
      { abstract (refine (total2_paths _ _);
        [ simpl; apply funextsec; intro b; refine (universalMapProperty _ _)
        | apply funextsec; intro b;
          apply funextsec; intro b';
          apply funextsec; intro f; simpl; apply setproperty ] ) using L. } }
    { abstract (intros p q e; apply nat_trans_eq;
                [ apply homset_property
                | intros b; apply (mapUniqueness _ (r b) _ (p ◽ b) (q ◽ b));
                  exact (maponpaths (λ k, pr1 k b) e)]) using M. } }
Defined.

Theorem functorPrecategoryLimits (B C:Precategory) : hasLimits C -> hasLimits [B,C].
Proof.
  intros lim I D.
  unfold hasLimits, Limit in lim.
  set (D' := bifunctor_comm _ _ _ D).
  assert (M := bifunctor_assoc_repn (cone_functor □ D') (λ b, lim I (D' ◾ b))); clear lim.
  exists (universalObject M).
  unfold Representation in M.


Abort.

Theorem functorPrecategoryColimits (B C:Precategory) : hasColimits C -> hasColimits [B,C].
Proof.
Abort.


(* --- *)