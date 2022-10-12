Require Export UniMath.Foundations.All.

(** *** Propositions equivalent to negations of propositions *)

Definition negProp P := ∑ Q, isaprop Q × (¬P <-> Q).

Definition negProp_to_isaprop {P} (nP : negProp P) : isaprop (pr1 nP)
  := pr1 (pr2 nP).

Definition negProp_to_hProp {P : UU} (Q : negProp P) : hProp.
Proof.
  intros. exists (pr1 Q). apply negProp_to_isaprop.
Defined.
Coercion negProp_to_hProp : negProp >-> hProp.

Definition negProp_to_iff {P} (nP : negProp P) : ¬P <-> nP
  := pr2 (pr2 nP).

Definition negProp_to_neg {P} {nP : negProp P} : nP -> ¬P.
Proof.
  intros np. exact (pr2 (negProp_to_iff nP) np).
Defined.

Coercion negProp_to_neg : negProp >-> Funclass.

Definition neg_to_negProp {P} {nP : negProp P} : ¬P -> nP.
Proof.
  intros np. exact (pr1 (negProp_to_iff nP) np).
Defined.

Definition negPred {X:UU} (x  :X) (P:∏ y:X, UU)      := ∏ y  , negProp (P y).

Definition negReln {X:UU}         (P:∏ (x y:X), UU)  := ∏ x y, negProp (P x y).

Definition neqProp {X:UU} (x y:X) :=            negProp (x=y).

Definition neqPred {X:UU} (x  :X) := ∏ y,       negProp (x=y).

Definition neqReln (X:UU)         := ∏ (x y:X), negProp (x=y).

Lemma negProp_to_complementary P : ∏ (Q : negProp P), P ⨿ Q <-> complementary P Q.
Proof.
  intros [Q [i [r s]]]; simpl in *.
  split.
  * intros pq. split.
    - intros p q. apply s.
      + assumption.
      + assumption.
    - assumption.
      * intros [j c].
        assumption.
Defined.

Lemma negProp_to_uniqueChoice P : ∏ (Q:negProp P), (isaprop P × (P ⨿ Q)) <-> iscontr (P ⨿ Q).
Proof.
  intros [Q [j [r s]]]; simpl in *. split.
  * intros [i v]. exists v. intro w.
    induction v as [v|v].
    - induction w as [w|w].
      + apply maponpaths, i.
      + contradicts (s w) v.
    - induction w as [w|w].
      + contradicts (s v) w.
      + apply maponpaths, j.
  * intros [c e]. split.
    - induction c as [c|c].
      + apply invproofirrelevance; intros p p'.
        exact (equality_by_case (e (ii1 p) @ !e (ii1 p'))).
      + apply invproofirrelevance; intros p p'.
        contradicts (s c) p.
    - exact c.
Defined.

(** Rework some foundational material using negative propositions. *)

Definition isisolated_ne (X:UU) (x:X) (neq_x:neqPred x) := ∏ y:X, (x=y) ⨿ neq_x y.

Definition isisolated_to_isisolated_ne {X x neq_x} :
  isisolated X x -> isisolated_ne X x neq_x.
Proof.
  intros i y. induction (i y) as [eq|ne].
  - exact (ii1 eq).
  - apply ii2. apply neg_to_negProp. assumption.
Defined.

Definition isisolated_ne_to_isisolated {X x neq_x} :
  isisolated_ne X x neq_x -> isisolated X x.
Proof.
  intros i y. induction (i y) as [eq|ne].
  - exact (ii1 eq).
  - apply ii2. use negProp_to_neg.
    + exact (neq_x y).
    + exact ne.
Defined.

Definition isolated_ne ( T : UU ) (neq:neqReln T) := ∑ t:T, isisolated_ne _ t (neq t).

Definition make_isolated_ne (T : UU) (t:T) (neq:neqReln T) (i:isisolated_ne _ t (neq t)) :
  isolated_ne T neq
  := (t,,i).

Definition pr1isolated_ne ( T : UU ) (neq:neqReln T) (x:isolated_ne T neq) : T := pr1 x.

Theorem isaproppathsfromisolated_ne (X : UU) (x : X) (neq_x : neqPred x)
        (is : isisolated_ne X x neq_x) (y : X)
  : isaprop (x = y).
Proof.
  (* we could follow the proof of isaproppathsfromisolated here, but we try a
     different way *)
  intros. unfold isisolated_ne in is. apply invproofirrelevance; intros m n.
  set (Q y := (x = y) ⨿ (neq_x y)).
  assert (a := (transport_section is m) @ !(transport_section is n)).
  induction (is x) as [j|k].
  - assert (b := transport_map (λ y p, ii1 p : Q y) m j); simpl in b;
      assert (c := transport_map (λ y p, ii1 p : Q y) n j); simpl in c.
    assert (d := equality_by_case (!b @ a @ c)); simpl in d.
    rewrite 2? transportf_id1 in d. apply (pathscomp_cancel_left j). assumption.
  - contradicts (neq_x x k) (idpath x).
Defined.

Definition compl_ne (X:UU) (x:X) (neq_x : neqPred x) := ∑ y, neq_x y.

Definition make_compl_ne (X : UU) (x : X) (neq_x : neqPred x) (y : X)
           (ne :neq_x y) :
  compl_ne X x neq_x := (y,,ne).

Definition pr1compl_ne (X : UU) (x : X) (neq_x : neqPred x)
           (c : compl_ne X x neq_x) :
  X := pr1 c.

Definition make_negProp {P : UU} : negProp P.
Proof.
  intros. exists (¬ P). split.
       - apply isapropneg.  (* uses [funextemptyAxiom] *)
       - apply isrefl_logeq.
Defined.

Definition make_neqProp {X : UU} (x y : X) : neqProp x y.
Proof.
  intros. apply make_negProp.
Defined.

Lemma isinclpr1compl_ne (X : UU) (x : X) (neq_x : neqPred x) :
  isincl (pr1compl_ne X x neq_x).
Proof.
  intros. apply isinclpr1. intro y. apply negProp_to_isaprop.
Defined.

Lemma compl_ne_weq_compl (X : UU) (x : X) (neq_x : neqPred x) :
  compl X x ≃ compl_ne X x neq_x.
Proof.
  (* uses [funextemptyAxiom] *)
  intros. apply weqfibtototal; intro y. apply weqiff.
  - apply negProp_to_iff.
  - apply isapropneg.
  - apply negProp_to_isaprop.
Defined.

Lemma compl_weq_compl_ne (X : UU) (x : X) (neq_x : neqPred x) :
  compl_ne X x neq_x ≃ compl X x.
Proof.
  (* uses [funextemptyAxiom] *)
  intros. apply weqfibtototal; intro y. apply weqiff.
  - apply issymm_logeq. apply negProp_to_iff.
  - apply negProp_to_isaprop.
  - apply isapropneg.
Defined.

Definition recompl_ne (X : UU) (x : X) (neq_x:neqPred x) :
  compl_ne X x neq_x ⨿ unit -> X.
Proof.
  intros w.
  induction w as [c|t].
  - exact (pr1compl_ne _ _ _ c).
  - exact x.
Defined.

Definition maponcomplincl_ne {X Y : UU} (f : X -> Y) (is : isincl f) (x : X)
           (neq_x : neqPred x) (neq_fx : neqPred (f x))
  : compl_ne X x neq_x -> compl_ne Y (f x) neq_fx.
Proof.
  intros c.
  set (x' := pr1 c).
  set (neqx := pr2 c).
  exact (f x',,neg_to_negProp (nP := neq_fx (f x'))
           (negf (invmaponpathsincl _ is x x') (negProp_to_neg neqx))).
Defined.

Definition weqoncompl_ne {X Y : UU} (w : X ≃ Y) (x : X) (neq_x : neqPred x)
           (neq_wx : neqPred (w x))
  : compl_ne X x neq_x ≃ compl_ne Y (w x) neq_wx.
Proof.
  intros. intermediate_weq (∑ x', neq_wx (w x')).
  - apply weqfibtototal; intro x'.
    apply weqiff.
    {apply (logeq_trans (Y := x != x')).
     {apply issymm_logeq, negProp_to_iff. }
     apply (logeq_trans (Y := w x != w x')).
     {apply logeqnegs. apply weq_to_iff. apply weqonpaths. }
     apply negProp_to_iff. }
    {apply negProp_to_isaprop. }
    {apply negProp_to_isaprop. }
  - refine (weqfp _ _).
Defined.

Definition weqoncompl_ne_compute {X Y : UU}
           (w : X ≃ Y) (x : X) (neq_x : neqPred x) (neq_wx : neqPred (w x)) x' :
  pr1 (weqoncompl_ne w x neq_x neq_wx x') = w (pr1 x').
Proof.
  intros. apply idpath.
Defined.

Definition invrecompl_ne (X : UU) (x : X) (neq_x : neqPred x)
           (is : isisolated X x) : X -> compl_ne X x neq_x ⨿ unit.
Proof.
  intros y. induction (is y) as [k|k].
  - exact (ii2 tt).
  - exact (ii1 (make_compl_ne X x neq_x y (neg_to_negProp k))).
Defined.

Theorem isweqrecompl_ne (X : UU) (x : X) (is : isisolated X x)
        (neq_x : neqPred x) : isweq (recompl_ne _ x neq_x).
Proof.
  (* does not use [funextemptyAxiom] *)
  intros.
  set (f := recompl_ne X x neq_x). set (g := invrecompl_ne X x neq_x is).
  refine (isweq_iso f g _ _).
  {intro u. induction (is (f u)) as [ eq | ne ].
   - induction u as [ c | u].
     + simpl. induction c as [ t neq ]; simpl; simpl in eq.
       contradicts (negProp_to_neg neq) eq.
     + induction u.
       intermediate_path (g x).
       {apply maponpaths. exact (pathsinv0 eq). }
       {unfold g, invrecompl_ne. induction (is x) as [ i | e ].
        {apply idpath. }
        {simpl. contradicts e (idpath x). }}
   - induction u as [ c | u ]. simpl.
     + induction c as [ y neq ]; simpl. unfold g, invrecompl_ne.
       induction (is y) as [ eq' | ne' ].
       {contradicts (negProp_to_neg neq) eq'. }
       {induction (ii2 ne') as [eq|neq'].
        {simpl. contradicts eq ne'. }
        {simpl. apply maponpaths. unfold make_compl_ne. apply maponpaths.
         apply proofirrelevance. exact (pr1 (pr2 (neq_x y))). }}
     + induction u. unfold f,g,invrecompl_ne;simpl.
       induction (is x) as [eq|neq].
       {simpl. apply idpath. }
       {apply fromempty. apply neq. apply idpath. }}
  {intro y. unfold f,g,invrecompl_ne;simpl.
   induction (is y) as [eq|neq].
   - induction eq. apply idpath.
   - simpl. apply idpath. }
Defined.

Theorem isweqrecompl_ne' (X : UU) (x : X) (is : isisolated X x)
        (neq_x : neqPred x) : isweq (recompl_ne _ x neq_x).
Proof.
  (* an alternative proof *)
  intros. set (f := recompl_ne X x neq_x). intro y.
  unfold neqPred,negProp in neq_x; unfold isisolated in is.
  apply (iscontrweqb (weqtotal2overcoprod _)). induction (is y) as [eq|ne].
  {induction eq. refine (iscontrweqf (weqii2withneg _ _) _).
   {intros z; induction z as [z e]; induction z as [z neq]; simpl in *.
    contradicts (!e) (negProp_to_neg neq). }
   {change x with (f (ii2 tt)). simple refine ((_,,_),,_).
    {exact tt. }
    {apply idpath. }
    {intro w. induction w as [t e]. unfold f in *; simpl in *. induction t.
     apply maponpaths. apply isaproppathsfromisolated. exact is. }}}
  {refine (iscontrweqf (weqii1withneg _ _) _).
   {intros z; induction z as [z e]; simpl in *. contradicts ne e. }
   {simple refine ((_,,_),,_).
    {exists y. apply neg_to_negProp. assumption. }
    {simpl. apply idpath. }
    intros z; induction z as [z e]; induction z as [z neq];
      induction e; simpl in *.
    induction (proofirrelevance _ (pr1 (pr2 (neq_x z))) neq
                                (neg_to_negProp ne)).
    apply idpath.
  }}
Defined.

Definition weqrecompl_ne (X : UU) (x : X) (is : isisolated X x)
           (neq_x : neqPred x) : compl_ne X x neq_x ⨿ unit ≃ X
  := make_weq _ (isweqrecompl_ne X x is neq_x).

Theorem isweqrecompl' (X : UU) (x : X) (is : isisolated X x) :
  isweq (recompl _ x).
Proof.
  (* alternative proof, spoils a computation if used in [weqrecompl], so unused *)
  intros. set (neq_x := λ y, make_neqProp x y).
  apply (isweqhomot (weqrecompl_ne X x is neq_x
                                   ∘ weqcoprodf (compl_ne_weq_compl X x neq_x)
                                   (idweq unit))%weq).
  {intro y. induction y as [y|t]; apply idpath. }
  apply weqproperty.
Defined.

Lemma iscotrans_to_istrans_negReln {X : UU} {R : hrel X} (NR : negReln R) :
  isdeccotrans R -> istrans NR.
(* uses no axioms; compare to istransnegrel *)
Proof.
  intros i ? ? ? nxy nyz. apply neg_to_negProp.
  apply (negf (i x1 x2 x3)). intro c. induction c as [c|c].
  - exact (negProp_to_neg nxy c).
  - exact (negProp_to_neg nyz c).
Defined.

Definition natneq (m n : nat) : negProp (m = n).
Proof.
  intros. exists (m ≠ n). split.
  - apply propproperty.
  - apply natneq_iff_neq.
Defined.

(* this replaces an earlier notation: *)
Notation " x ≠ y " := (natneq x y) (at level 70, no associativity) : nat_scope.

Definition nat_compl (i : nat) := compl_ne _ i (λ j, i ≠ j).

Theorem weqdicompl (i : nat) : nat ≃ nat_compl i.
Proof.
  use weq_iso.
  - intro j. exists (di i j). apply di_neq_i.
  - intro j. exact (si i (pr1 j)).
  - simpl. intro j. unfold di. induction (natlthorgeh j i) as [lt|ge].
    + unfold si. induction (natlthorgeh i j) as [lt'|ge'].
      * contradicts (isasymmnatlth _ _ lt') lt.
      * apply idpath.
    + unfold si. induction (natlthorgeh i (S j)) as [lt'|ge'].
      * change (S j) with (1 + j). rewrite natpluscomm. apply plusminusnmm.
      * unfold natgeh,natleh in ge. contradicts (natlehneggth ge') ge.
  - simpl. intro j. induction j as [j ne]; simpl.
    apply subtypePath.
    + intro k. apply negProp_to_isaprop.
    + simpl. unfold si. induction (natlthorgeh j i) as [lt|ge].
      * clear ne.
        induction (natlthorgeh i j) as [lt'|_].
        { contradicts (isasymmnatlth _ _ lt') lt. }
        { unfold di. induction (natlthorgeh j i) as [lt'|ge'].
          - apply idpath.
          - contradicts (natgehtonegnatlth _ _ ge') lt. }
      * assert (lt := natleh_neq ge ne); clear ne ge.
        induction (natlthorgeh i j) as [_|ge'].
        { unfold di. induction (natlthorgeh (j - 1) i) as [lt'|ge'].
          - apply fromempty. induction j as [|j _].
            + exact (negnatlthn0 _ lt).
            + change (S j) with (1 + j) in lt'.
                 rewrite natpluscomm in lt'.
                 rewrite plusminusnmm in lt'.
                 change (i < S j) with (i ≤ j) in lt.
                 exact (natlehneggth lt lt').
          - induction j as [|j _].
            + contradicts (negnatlthn0 i) lt.
            + simpl. apply maponpaths. apply natminuseqn. }
        contradicts (natgehtonegnatlth _ _ ge') lt.
Defined.
