Require Export UniMath.Combinatorics.Lists.
Require Export UniMath.Combinatorics.FiniteSequences.
Require Export UniMath.Algebra.Monoids_and_Groups.
Require Export UniMath.Foundations.UnivalenceAxiom.
Unset Automatic Introduction.

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

(** general associativity for monoids *)

Local Open Scope multmonoid.

(* we define iterated products in the same way now, with left associativity: *)
Definition sequenceProduct {M:monoid} : Sequence M -> M.
Proof.
  intros ? [n x].
  induction n as [|n sequenceProduct].
  { exact 1. }
  { exact (sequenceProduct (pr2 (drop (S n,,x) (negpathssx0 _))) * x (lastelement _)). }
Defined.

(* alternate versions with ' attempted with lists instead of sequences *)
Definition monoidProduct {M:monoid} : list M -> M.
Proof.
  intros ?.
  exact (foldr op 1).
Defined.

Definition doubleProduct {M:monoid} : Sequence (Sequence M) -> M.
Proof.
  intros ? [n x].
  induction n as [|n doubleProduct].
  { exact 1. }
  { exact ((doubleProduct (x ∘ dni_lastelement) * sequenceProduct (x (lastelement _)))). }
Defined.

Definition doubleProduct' {M:monoid} : list (list M) -> M.
Proof.
  intros M.
  apply list_ind.
  + exact 1.
  + intros x _ m. exact (monoidProduct x * m).
Defined.

(* some rewriting rules *)

Definition sequenceProductStep {M:monoid} {n} (x:stn (S n) -> M) :
  sequenceProduct (S n,,x) = sequenceProduct (n,,x ∘ dni_lastelement) * x (lastelement _).
Proof. intros. reflexivity. Defined.

Definition sequenceProductStep' {M:monoid} (x:M) (xs:list M) :
  monoidProduct (x::xs) = x * monoidProduct xs.
Proof.
  intros.
  induction xs.
  reflexivity.
Defined.

Local Definition sequenceProduct_append {M:monoid} (x:Sequence M) (m:M) :
  sequenceProduct (append x m) = sequenceProduct x * m.
Proof. intros ? [n x] ?. unfold append. rewrite sequenceProductStep.
       unfold funcomp, lastelement.
       Local Opaque sequenceProduct. simpl. Transparent sequenceProduct.
       induction (natlehchoice4 n n (natgthsnn n)) as [p|p].
       { contradicts (isirreflnatlth n) p. }
       { change ((n,, natgthsnn n):stn (S n)) with (lastelement n).
         rewrite append_fun_compute_2.
         apply (maponpaths (λ a, a * m)).
         apply (maponpaths (λ x, sequenceProduct (n,,x))).
         apply funextfun; intros [i b]; simpl.
         now rewrite append_fun_compute_1. }
Defined.

Local Definition doubleProductStep {M:monoid} {n} (x:stn (S n) -> Sequence M) :
  doubleProduct (S n,,x) = doubleProduct (n,,x ∘ dni_lastelement) * sequenceProduct (x (lastelement _)).
Proof. intros. reflexivity. Defined.

(* The general associativity theorem. *)


Theorem associativityOfProducts {M:monoid} (x:Sequence (Sequence M)) :
  sequenceProduct (flatten x) = doubleProduct x.
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  intros ? [n x].
  induction n as [|n IHn].
  { reflexivity. }
  (* { rewrite flattenStep, doubleProductStep. *)
  (*   generalize (x (lastelement _)) as z. *)
  (*   generalize (x ∘ dni_lastelement) as y. *)
  (*   intros y [m z]. *)
  (*   induction m as [|m IHm]. *)
  (*   { change (sequenceProduct (0,, z)) with (unel M). rewrite runax. *)
(*       change (concatenate (flatten (n,, y)) (0,, z)) with (flatten (n,, y)). *)
(*       exact (IHn y). } *)
(*     { rewrite sequenceProductStep, concatenateStep. *)
(*       generalize (z (lastelement m)) as w; generalize (z ∘ dni _ (lastelement _)) as v; intros. *)
(*       rewrite <- assocax. *)
(*       rewrite sequenceProduct_append. *)
(*       apply (maponpaths (λ u, u*w)). *)
(*       apply IHm. } } *)
(* Defined. *)
Abort.

Theorem associativityOfProducts {M:monoid} (x:list (list M)) :
  monoidProduct (Lists.flatten x) = doubleProduct' x.
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  intros M.
  simple refine (list_ind _ _ _).
  - simpl.
    reflexivity.
  - intros x xs ind.
    simpl in ind.
    cbn beta.
    unfold Lists.flatten, doubleProduct'.
    rewrite 2 list_ind_compute_2.
    fold (doubleProduct' xs).
    fold (Lists.flatten xs).
    intermediate_path (monoidProduct x * monoidProduct (Lists.flatten xs)).
    + generalize (Lists.flatten xs) as y; clear xs ind; intro y.
      generalize x; clear x.
      apply list_ind.
      * cbn. apply pathsinv0, lunax.
      * intros x xs e.
        rewrite Lists.concatenateStep.
        rewrite 2 sequenceProductStep'.
        rewrite assocax.
        apply maponpaths.
        exact e.
    + apply maponpaths.
      exact ind.
Defined.

(** commutativity *)

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  sequenceProduct (n,,x) = sequenceProduct (n,,x∘f).
Proof.
  (** This proof comes from % \cite[section 1.5, Theorem 2, page 9]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  intros.
  induction n as [|n IH].
  - reflexivity.
  - assert (specialcase : Π (y:stn _->M) (g : stn _ ≃ stn _), g (lastelement n) = lastelement n ->
        sequenceProduct (S n,, y) = sequenceProduct (S n,, y ∘ g)).
    { intros ? ? a. rewrite 2? sequenceProductStep. change ((_ ∘ _) _) with (y (g (lastelement n))).
      rewrite a. apply (maponpaths (λ m, m * _)). change (_ ∘ _ ∘ _) with (y ∘ (g ∘ dni_lastelement)).
      set (h := eqweqmap (maponpaths stn_compl a)).
      assert (pr1_h : Π i, pr1 (pr1 (h i)) = pr1 (pr1 i)). { intros. induction a. reflexivity. }
      set (wc := weqdnicompl n (lastelement n)).
      set (g' := (invweq wc ∘ (h ∘ (weqoncompl_ne g (lastelement n) (stnneq _) (stnneq _) ∘ wc))) %weq).
      intermediate_path (sequenceProduct (n,, y ∘ dni_lastelement ∘ g')).
      { apply IH. }
      { change ((_ ∘ _) ∘ _) with (y ∘ (dni_lastelement ∘ g')).
        apply maponpaths; apply maponpaths; apply (maponpaths (λ g, _ ∘ g)).
        apply funextfun; intros i.
        unfold funcomp. apply isinjstntonat. rewrite pr1_dni_lastelement. unfold g'.
        rewrite 3? weqcomp_to_funcomp_app. rewrite inv_weqdnicompl_compute_last. rewrite pr1_h.
        unfold pr1weq.
        unfold weqoncompl_ne.
        (* change (pr1 *)
        (*    (weqpair *)
        (*       (maponcomplweq_ne g (lastelement n)  *)
        (*          (stnneq (lastelement n)) (stnneq (pr1 g (lastelement n)))) *)
        (*       (isweqmaponcompl_ne g (lastelement n) *)
        (*          (stnneq (lastelement n)) (stnneq (pr1 g (lastelement n))))) *)
        (*    (pr1 wc i)) *)
        (* with (maponcomplweq_ne g (lastelement n)  *)
        (*                        (stnneq (lastelement n)) (stnneq (pr1 g (lastelement n))) *)
        (*                        (pr1 wc i) *)
        (*      ). *)
        (* unfold wc. *)
        (* unfold weqdnicompl. *)

        (* induction (natlthorgeh j (lastelement n)) as [t|t]. *)

        (* rewrite weqdnicompl_compute_last. *) (* rewrite pr1_dni_lastelement. *)
        (* reflexivity. *)
        admit.
      }}
    set (j := f (lastelement n)).
    induction j as [j jlt].
    assert (jle := natlthsntoleh _ _ jlt).
    Local Open Scope nat.
    set (m := nil □ j □ 1 □ n-j).
    set (m' := nil □ j □ n-j □ 1).
    set (sw := (nil □ ●0 □ ●2 □ ●1 : Sequence (stn 3)) % stn).
    assert (B : stnsum m = S n).
    { unfold stnsum; simpl. repeat unfold append_fun; simpl. rewrite natplusassoc. rewrite (natpluscomm 1). rewrite <- natplusassoc.
      rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. }
    assert (B' : stnsum m' = S n).
    { unfold stnsum; simpl. rewrite natplusassoc. rewrite (natpluscomm _ 1). rewrite <- natplusassoc. apply B. }
    assert (C : m' ∘ sw ~ m).
    { intro i. change (pr1 sw) with 3 in i.
      induction i as [i b]. inductive_reflexivity i b. }
    assert (isweqsw : isweq sw).
    { refine (gradth sw sw _ _); ( intros [i b]; inductive_reflexivity i b). }
    set (w := weqstnsum1 m). rewrite B in w. change (pr1 m) with 3 in w.
    set (w' := weqstnsum1 m'). rewrite B' in w'. change (pr1 m') with 3 in w'.

(*
    induction (isdeceqstn (S n) (f (lastelement n)) (lastelement n)) as [p|p].
    + now apply specialcase.
    +
*)

Abort.
