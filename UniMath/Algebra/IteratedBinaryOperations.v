Require Export UniMath.Combinatorics.Lists.
Require Export UniMath.Combinatorics.FiniteSequences.
Require Export UniMath.Algebra.Monoids_and_Groups.
Require Export UniMath.Foundations.UnivalenceAxiom.
Unset Automatic Introduction.

(* move upstream *)

Local Arguments dni {_} _ _.

Local Arguments firstelement {_}. (* make non local *)

Local Arguments lastelement {_}. (* make non local *)

(* end of move upstream *)

Local Notation "[]" := Lists.nil (at level 0, format "[]").
Local Infix "::" := cons.

(** general associativity for binary operations on types *)

Section BinaryOperations.

  Context {X:UU} (unit:X) (op:binop X).

  (* we use an extra induction step in each of the following definitions so
     we don't end up with superfluous unit factors *)

  Definition product_list : list X -> X.
  Proof.
    intro k.
    simple refine (list_ind (λ _, X) _ _ k).
    - simpl. exact unit.
    - intros x m _.
      generalize x; clear x.
      simple refine (list_ind (λ _, X -> X) _ _ m).
      + simpl. intro x. exact x.
      + simpl. intros y _ z x. exact (op x (z y)).
  Defined.

  Definition product_fun {n} (x:stn n->X) : X.
  Proof.
    intros.
    induction n as [|n _].
    { exact unit. }
    { induction n as [|n I].
      { exact (x firstelement). }
      { exact (op (I (x ∘ dni_lastelement)) (x lastelement)). }}
  Defined.

  Definition product_seq : Sequence X -> X.
  Proof.
    intros x.
    exact (product_fun x).
  Defined.

  (* now define products of products *)

  Definition prodprod_list : list(list X) -> X.
  Proof.
    intros w.
    exact (product_list (map product_list w)).
  Defined.

  Definition prodprod_fun {n} {m:stn n -> nat} : (∏ i (j:stn (m i)), X) -> X.
  Proof.
    intros ? ? x.
    exact (product_fun (λ i, product_fun (x i))).
  Defined.

  Definition prodprod_seq : Sequence (Sequence X) -> X.
  Proof.
    intros x.
    exact (prodprod_fun (λ i j, x i j)).
  Defined.

  Definition isAssociative_list := ∏ (x:list (list X)), product_list (Lists.flatten x) = prodprod_list x.

  Definition isAssociative_fun :=
    ∏ n (m:stn n -> nat) (x : ∏ i (j:stn (m i)), X), product_fun (FiniteSequences.flatten' x) = prodprod_fun x.

  Definition isAssociative_seq :=
    ∏ (x : Sequence (Sequence X)), product_seq (FiniteSequences.flatten x) = prodprod_seq x.

  Lemma assoc_fun_to_seq : isAssociative_fun -> isAssociative_seq.
  Proof.
    intros assoc x.
    exact (assoc _ _ (λ i j, x i j)).
  Defined.

  Definition product_list_step (runax : isrunit op unit) (x:X) (xs:list X) :
    product_list (x::xs) = op x (product_list xs).
  Proof.
    intros runax x xs.
    generalize x; clear x.
    apply (list_ind (λ xs, ∏ x : X, product_list (x :: xs) = op x (product_list xs))).
    { intro x. simpl. apply pathsinv0,runax. }
    intros y rest IH x.
    reflexivity.
  Defined.

End BinaryOperations.

(** general associativity for monoids *)

Local Open Scope multmonoid.

Definition product_list_mon {M:monoid} : list M -> M.
Proof.
  intros ? x.
  exact (product_list (unel M) (@op M) x).
Defined.

Definition product_seq_mon {M:monoid} : Sequence M -> M.
Proof.
  intros ? x.
  exact (product_seq (unel M) (@op M) x).
Defined.

Definition prodprod_seq_mon {M:monoid} : Sequence (Sequence M) -> M.
Proof.
  intros ? x.
  exact (prodprod_seq (unel M) (@op M) x).
Defined.

Definition prodprod_list_mon {M:monoid} : list (list M) -> M.
Proof.
  intros ? x.
  exact (prodprod_list (unel M) (@op M) x).
Defined.

(* some rewriting rules *)

Definition product_seq_mon_step {M:monoid} {n} (x:stn (S n) -> M) :
  product_seq_mon (S n,,x) = product_seq_mon (n,,x ∘ dni_lastelement) * x lastelement.
Proof.
  intros.
  induction n as [|n _].
  { apply pathsinv0, lunax. }
  reflexivity.
Defined.

Definition product_list_mon_step {M:monoid} (x:M) (xs:list M) :
  product_list_mon (x::xs) = x * product_list_mon xs.
Proof.
  intros M x xs.
  apply product_list_step.
  apply runax.
Defined.

Local Definition product_seq_mon_append {M:monoid} (x:Sequence M) (m:M) :
  product_seq_mon (append x m) = product_seq_mon x * m.
Proof.
   intros ? [n x] ?. unfold append. rewrite product_seq_mon_step.
   rewrite append_fun_compute_2.
   apply (maponpaths (λ a, a * m)).
   apply (maponpaths (λ x, product_seq_mon (n,,x))).
   apply funextfun; intros [i b]; simpl.
   unfold funcomp.
   now rewrite append_fun_compute_1.
Defined.

Local Definition prodprod_step {M:monoid} {n} (x:stn (S n) -> Sequence M) :
  prodprod_seq_mon (S n,,x) = prodprod_seq_mon (n,,x ∘ dni_lastelement) * product_seq_mon (x lastelement).
Proof.
  intros.
  induction n as [|n _].
  - simpl. apply pathsinv0,lunax.
  - reflexivity.
Defined.

(* The general associativity theorem. *)


Theorem associativityOfProducts {M:monoid} (x:Sequence (Sequence M)) :
  product_seq_mon (flatten x) = prodprod_seq_mon x.
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  intros ? [n x].
  induction n as [|n IHn].
  { reflexivity. }
  (* { rewrite flattenStep, prodprod_step. *)
  (*   generalize (x lastelement) as z. *)
  (*   generalize (x ∘ dni_lastelement) as y. *)
  (*   intros y [m z]. *)
  (*   induction m as [|m IHm]. *)
  (*   { change (product_seq_mon (0,, z)) with (unel M). rewrite runax. *)
(*       change (concatenate (flatten (n,, y)) (0,, z)) with (flatten (n,, y)). *)
(*       exact (IHn y). } *)
(*     { rewrite product_seq_mon_step, concatenateStep. *)
(*       generalize (z lastelement) as w; generalize (z ∘ dni _ lastelement) as v; intros. *)
(*       rewrite <- assocax. *)
(*       rewrite product_seq_mon_append. *)
(*       apply (maponpaths (λ u, u*w)). *)
(*       apply IHm. } } *)
(* Defined. *)
Abort.

Theorem associativityOfProducts {M:monoid} (x:list (list M)) :
  product_list_mon (Lists.flatten x) = prodprod_list_mon x.
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  intros M.
  apply list_ind.
  - simpl. reflexivity.
  - intros x xs ind. simpl in ind. cbn beta.
    rewrite Lists.flattenStep.
    unfold prodprod_list_mon. unfold prodprod_list.
    rewrite mapStep.
    rewrite (product_list_step _ _ (runax M)).
    intermediate_path (product_list_mon x * product_list_mon (Lists.flatten xs)).
    + generalize (Lists.flatten xs) as y; clear xs ind; intro y.
      generalize x; clear x.
      apply list_ind.
      * cbn. apply pathsinv0, lunax.
      * intros x xs e. rewrite Lists.concatenateStep.
        rewrite product_list_mon_step. rewrite product_list_mon_step.
        rewrite assocax. apply maponpaths. exact e.
    + apply maponpaths. exact ind.
Defined.

(** commutativity *)

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  product_seq_mon (n,,x) = product_seq_mon (n,,x∘f).
Proof.
  (** This proof comes from % \cite[section 1.5, Theorem 2, page 9]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  intros.
  induction n as [|n IH].
  - reflexivity.
  - assert (specialcase : ∏ (y:stn _->M) (g : stn _ ≃ stn _), g lastelement = lastelement ->
        product_seq_mon (S n,, y) = product_seq_mon (S n,, y ∘ g)).
    { intros ? ? a. rewrite 2? product_seq_mon_step. change ((_ ∘ _) _) with (y (g lastelement)).
      rewrite a. apply (maponpaths (λ m, m * _)). change (_ ∘ _ ∘ _) with (y ∘ (g ∘ dni_lastelement)).
      set (h := eqweqmap (maponpaths stn_compl a)).
      assert (pr1_h : ∏ i, pr1 (pr1 (h i)) = pr1 (pr1 i)). { intros. induction a. reflexivity. }
      set (wc := weqdnicompl n lastelement).
      set (g' := (invweq wc ∘ (h ∘ (weqoncompl_ne g lastelement (stnneq _) (stnneq _) ∘ wc))) %weq).
      intermediate_path (product_seq_mon (n,, y ∘ dni_lastelement ∘ g')).
      { apply IH. }
      { change ((_ ∘ _) ∘ _) with (y ∘ (dni_lastelement ∘ g')).
        apply maponpaths; apply maponpaths.
        apply (maponpaths (λ h i, y(h i))).
        apply funextfun; intros i.
        unfold funcomp. apply isinjstntonat. rewrite pr1_dni_lastelement. unfold g'.
        rewrite 3? weqcomp_to_funcomp_app. rewrite inv_weqdnicompl_compute_last. rewrite pr1_h.
        unfold pr1weq.
        unfold weqoncompl_ne.
        (* change (pr1 *)
        (*    (weqpair *)
        (*       (maponcomplweq_ne g lastelement  *)
        (*          (stnneq lastelement) (stnneq (pr1 g lastelement))) *)
        (*       (isweqmaponcompl_ne g lastelement *)
        (*          (stnneq lastelement) (stnneq (pr1 g lastelement)))) *)
        (*    (pr1 wc i)) *)
        (* with (maponcomplweq_ne g lastelement  *)
        (*                        (stnneq lastelement) (stnneq (pr1 g lastelement)) *)
        (*                        (pr1 wc i) *)
        (*      ). *)
        (* unfold wc. *)
        (* unfold weqdnicompl. *)

        (* induction (natlthorgeh j lastelement) as [t|t]. *)

        (* rewrite weqdnicompl_compute_last. *) (* rewrite pr1_dni_lastelement. *)
        (* reflexivity. *)
        admit.
      }}
    set (j := f lastelement).
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
    induction (isdeceqstn (S n) (f lastelement) lastelement) as [p|p].
    + now apply specialcase.
    +
*)

Abort.
