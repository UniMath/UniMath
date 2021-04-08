(**

Tom de Jong

Created: November 2018

Refactored: January 2019

*******************************************************************************)

(** * Directed complete posets and least fixed points *)
(** ** Contents
- Least upper bounds ([leastupperbound])
- Definition of a directed family ([directedfamily])
- Definition of a directed complete poset (dcpo) ([dcpo])
- Definition of a morphisms of dcpos ([morphismofdcpos])
- The morphisms between two dcpos form a dcpo with the pointwise order
  ([morphismsofdcpos_formdcpo])
- Definition of a dcpo with bottom ([dcpowithbottom])
- The least fixed point operator for morphisms between dcpos with bottom
  ([leastfixedpoint])
*)

Require Import UniMath.Foundations.All.

Local Open Scope poset. (* So we can write ≤ *)

(** ** Least upper bounds *)
Section leastupperbound.
Context {X : Poset}.
Context {I : UU}.
Variable (f : I -> X). (* Indexing family *)

Definition isupperbound (u : X) : UU := ∏ (i : I), f i ≤ u.
Lemma isaprop_isupperbound (u : X) : isaprop (isupperbound u).
Proof.
  apply impred_isaprop; intro i; apply propproperty.
Qed.

(* Definition of least upper bound (lub) *)
Definition islub (u : X) : UU := isupperbound u ×
                                 ∏ (y : X), (∏ (i : I), f i ≤ y) -> u ≤ y.
Lemma isaprop_islub (u : X) : isaprop (islub u).
Proof.
  apply isapropdirprod.
  - apply isaprop_isupperbound.
  - apply impred_isaprop; intro x.
    apply isapropimpl; apply propproperty.
Qed.

Definition islub_isupperbound {u : X} : islub u -> isupperbound u := pr1.
Definition islub_isleast {u : X} :
  islub u -> ∏ (y : X), (∏ (i : I), f i ≤ y) -> u ≤ y := pr2.

Lemma lubsareunique {u v : X} : islub u -> islub v -> u = v.
Proof.
  intros islubu islubv.
  apply isantisymm_posetRelation.
  - apply (islub_isleast islubu). exact (islub_isupperbound islubv).
  - apply (islub_isleast islubv). exact (islub_isupperbound islubu).
Qed.

End leastupperbound.

(** ** Directed families *)
Section directedfamily.
Context {X : Poset}.
Context {I : UU}.

Definition isdirected (f : I -> X) : UU :=
  ∥ I ∥ × ∏ (i j : I), ∥∑ (k : I), f i ≤ f k × f j ≤ f k∥.
Lemma isaprop_isdirected (f : I -> X) : isaprop (isdirected f).
Proof.
  apply isapropdirprod.
  - apply isapropishinh.
  - apply impred_isaprop; intro i; apply impred_isaprop; intro j.
    apply isapropishinh.
Qed.

Definition directeduntruncated (f : I -> X) (i j : I) : UU :=
  ∑ (k : I), f i ≤ f k × f j ≤ f k.

Definition isdirected_inhabited {f : I -> X} :
  isdirected f -> ∥ I  ∥ := pr1.
Definition isdirected_order {f : I -> X} :
  isdirected f -> ∏ (i j : I), ∥∑ (k : I), f i ≤ f k × f j ≤ f k∥ := pr2.

End directedfamily.

(** ** Directed complete posets (dcpos) *)
Section dcpo.
Definition isdirectedcomplete (X : Poset) : UU :=
  ∏ (I : UU) (f : I -> X), isdirected f -> ∑ (u : X), islub f u.
Lemma isaprop_isdirectedcomplete (X : Poset) : isaprop (isdirectedcomplete X).
Proof.
  apply impred_isaprop; intro I.
  apply impred_isaprop; intro f.
  apply isapropimpl.
  apply invproofirrelevance.
  intros [u p] [v q].
  apply total2_paths_equiv.
  exists (lubsareunique _ p q).
  apply proofirrelevance. apply isaprop_islub.
Qed.

Definition dcpo := ∑ (X : Poset), isdirectedcomplete X.
Definition dcpoposet : dcpo -> Poset := pr1.
Coercion dcpoposet : dcpo >-> Poset.
Definition dcpoisdirectedcomplete (D : dcpo) : isdirectedcomplete D := pr2 D.
Definition make_dcpo (X : Poset) (i : isdirectedcomplete X) : dcpo := (X,,i).

Definition dcpo_mklub {D : dcpo} {I : UU} {f : I -> D} : isdirected f -> D.
Proof.
  intro isdirec.
  exact (pr1 (dcpoisdirectedcomplete D I f isdirec)).
Defined.

Definition dcpo_mklub_islub {D : dcpo} {I : UU} {f : I -> D}
           (isdirec : isdirected f) : islub f (dcpo_mklub isdirec).
Proof.
  exact (pr2 (dcpoisdirectedcomplete D I f isdirec)).
Defined.

End dcpo.

(** ** Morphisms of dcpos *)

Section morphismofdcpos.
Definition preserveslub {P Q : Poset} (f : P -> Q) {I : UU} (u : I -> P) : UU :=
  ∏ (v : P), islub u v -> islub (f ∘ u) (f v).
Lemma isaprop_preserveslub {P Q : Poset} (f : P -> Q) {I : UU} (u : I -> P) :
  isaprop (preserveslub f u).
Proof.
  apply impred_isaprop; intro v.
  apply isapropimpl. apply isaprop_islub.
Qed.

Definition isdcpomorphism {D D' : dcpo} (f : D -> D') :=
  isaposetmorphism f ×
  ∏ (I : UU) (u : I -> D), isdirected u -> preserveslub f u.
Lemma isaprop_isdcpomorphism {D D' : dcpo} (f : D -> D') :
  isaprop (isdcpomorphism f).
Proof.
  apply isapropdirprod.
  - apply isaprop_isaposetmorphism.
  - apply impred_isaprop; intro I.
    apply impred_isaprop; intro u.
    apply isapropimpl; apply isaprop_preserveslub.
Qed.

Definition dcpomorphism (D D' : dcpo) := ∑ (f : D -> D'), isdcpomorphism f.

Definition dcpomorphism_posetmorphism (D D' : dcpo) :
  dcpomorphism D D' -> posetmorphism D D'.
Proof.
  intros [f isdcpomor].
  exists f. exact (pr1 isdcpomor).
Defined.
Coercion dcpomorphism_posetmorphism : dcpomorphism >-> posetmorphism.

Lemma dcpomorphism_preservesorder {D D' : dcpo} (f : dcpomorphism D D') :
  isaposetmorphism f.
Proof.
  exact (pr1 (pr2 f)).
Qed.

Lemma dcpomorphism_preservesdirected {D D' : dcpo} (f : dcpomorphism D D')
      {I : UU} {u : I -> D} : isdirected u -> isdirected (pr1 f ∘ u).
Proof.
  intro isdirec.
  split.
  - exact (isdirected_inhabited isdirec).
  - intros i j. apply (@factor_through_squash (directeduntruncated u i j)).
    + apply isapropishinh.
    + intro direc. apply hinhpr. induction direc as [k ineqs].
      split with k. split.
      * apply dcpomorphism_preservesorder. exact (pr1 ineqs).
      * apply dcpomorphism_preservesorder. exact (pr2 ineqs).
    + exact (isdirected_order isdirec i j).
Qed.

Lemma dcpomorphism_preserveslub {D D' : dcpo} (f : dcpomorphism D D')
           {I : UU} {u : I -> D} : isdirected u -> preserveslub f u.
Proof.
  intro isdirec.
  apply (pr2 (pr2 f)).
  exact isdirec.
Qed.

(* In fact, requiring that a dcpo morphism is a poset morphism is redundant *)
Definition isdcpomorphism' {D D' : dcpo} (f : D -> D') :=
  ∏ (I : UU) (u : I -> D), isdirected u -> preserveslub f u.

Lemma preservesdirectedlub_isdcpomorphism {D D' : dcpo} (f : D -> D') :
  isdcpomorphism' f -> isdcpomorphism f.
Proof.
  intro preservesdireclub.
  split.
  - intros x y ineq.
    set (two := coprod unit unit).
    set (fam := (λ t : two, match t with | inl _ => x | inr _ => y end)).
    assert (isdirec : isdirected fam).
    { split.
      - apply hinhpr. exact (inl tt).
      - intros i j. apply hinhpr. exists (inr tt).
        induction i, j.
        + simpl. exact (ineq,,ineq).
        + simpl. split.
          ++ exact ineq.
          ++ apply isrefl_posetRelation.
        + simpl. split.
          ++ apply isrefl_posetRelation.
          ++ exact ineq.
        + simpl. split.
          ++ apply isrefl_posetRelation.
          ++ apply isrefl_posetRelation. }
    assert (islubfam : islub fam y).
    { split.
      - intro t. induction t.
        + simpl. exact ineq.
        + simpl. apply isrefl_posetRelation.
      - intros d ineqs. exact (ineqs (inr tt)). }
    set (islubfam' := preservesdireclub two fam isdirec y islubfam).
    apply (islub_isupperbound (f ∘ fam) islubfam' (inl tt)).
  - exact preservesdireclub.
Qed.

Definition mkdcpomorphism {D D' : dcpo}
           (f : D -> D') (i : isdcpomorphism' f) : dcpomorphism D D'.
Proof.
  exists f.
  apply preservesdirectedlub_isdcpomorphism. exact i.
Defined.

(** Constant functions between dcpos are continuous *)
Definition mkconst_dcpomor (D E : dcpo) (e : E) : dcpomorphism D E.
Proof.
  use mkdcpomorphism.
  - exact (λ _, e).
  - intros I u isdirec v islubv. split.
    + intro i. simpl. apply isrefl_posetRelation.
    + intros d' ineqs. apply (@factor_through_squash I).
      * apply propproperty.
      * intro i. exact (ineqs i).
      * exact (isdirected_inhabited isdirec).
Defined.

End morphismofdcpos.

(** ** The morphisms between two dcpos form a dcpo with the pointwise order. *)
Section morphismsofdcpos_formdcpo.
Definition pointwiseorder (D D' : dcpo) : hrel (dcpomorphism D D').
Proof.
  intros f g. use make_hProp.
  - exact (∏ (d : D), f d ≤ g d).
  - apply impred_isaprop; intro d. apply propproperty.
Defined.

Lemma ispartialorder_pointwiseorder (D D' : dcpo) :
  isPartialOrder (pointwiseorder D D').
Proof.
  split.
  - split.
    + intros f g h ineq1 ineq2 d.
      eapply istrans_posetRelation.
      ++ use ineq1.
      ++ use ineq2.
    + intros f p. apply isrefl_posetRelation.
  - intros f g ineq1 ineq2. apply total2_paths_equiv.
    assert (funeq : pr1 f = pr1 g).
    { use funextfun; intro d. apply isantisymm_posetRelation.
      - use ineq1.
      - use ineq2. }
    exists funeq.
    apply proofirrelevance, isaprop_isdcpomorphism.
Qed.

Definition posetofdcpomorphisms (D D' : dcpo) : Poset.
Proof.
  use make_Poset.
  - use make_hSet.
    + exact (dcpomorphism D D').
    + apply (isofhleveltotal2 2).
      ++ apply impred_isaset; intro d.
         apply setproperty.
      ++ intro f; apply isasetaprop, isaprop_isdcpomorphism.
  - use make_PartialOrder.
    + apply pointwiseorder.
    + apply ispartialorder_pointwiseorder.
Defined.

Lemma lubpreservesorder {X : Poset} {I : UU} (u v : I -> X) :
  (∏ (i : I), u i ≤ v i) ->
  ∏ (lu lv : X), islub u lu -> islub v lv -> lu ≤ lv.
Proof.
  intros ineqs lu lv islubu islubv.
  eapply islub_isleast.
  - exact islubu.
  - intro i. eapply istrans_posetRelation.
    + exact (ineqs i).
    + apply (islub_isupperbound v islubv).
Qed.

(** Given a family of dcpo morphisms from D to D' and a point d : D
   we have a pointwise family in D' by evaluating each morphism at d. *)
Definition pointwisefamily {D D' : dcpo} {I : UU}
           (F : I -> dcpomorphism D D') : D -> I -> D' :=
  λ (d : D), λ (i : I), (F i) d.

Lemma pointwisefamily_isdirected {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') :
  isdirected F -> ∏ (d : D), isdirected (pointwisefamily F d).
Proof.
  intros isdirec d. split.
  - exact (isdirected_inhabited isdirec).
  - intros i j. use factor_through_squash.
    + exact (directeduntruncated F i j).
    + apply isapropishinh.
    + intro direc. apply hinhpr.
      induction direc as [k ineqs].
      exists k. unfold pointwisefamily.
      induction ineqs as [ineq1 ineq2]. split.
      * use ineq1.
      * use ineq2.
    + apply (isdirected_order isdirec).
Qed.

Definition pointwiselub {D D' : dcpo} {I : UU}
           (F : I -> posetofdcpomorphisms D D') (isdir : isdirected F) : D -> D'.
Proof.
  intro d.
  set (ptfamdir := pointwisefamily_isdirected F isdir d).
  exact (dcpo_mklub ptfamdir).
Defined.

Lemma pointwiselub_islubpointwise {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  ∏ (d : D), islub (pointwisefamily F d) (pointwiselub F isdirec d).
Proof.
  intro d.
  set (ptfamdir := pointwisefamily_isdirected F isdirec d).
  exact (dcpo_mklub_islub ptfamdir).
Qed.

Lemma pointwiselub_preservesorder {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  isaposetmorphism (pointwiselub F isdirec).
Proof.
  intros x y ineq. use lubpreservesorder.
  - exact I.
  - intro i. apply (F i). exact x.
  - intro i. apply (F i). exact y.
  - intro i. simpl.
    apply dcpomorphism_preservesorder.
    exact ineq.
  - simpl. apply pointwiselub_islubpointwise.
  - simpl. apply pointwiselub_islubpointwise.
Qed.

Lemma pointwiselub_isdcpomorphism' {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  isdcpomorphism' (pointwiselub F isdirec).
Proof.
  unfold isdcpomorphism'. intros J v isdirecv.
  intros w wislub.
  split.
  - intro j. apply pointwiselub_preservesorder.
    apply islub_isupperbound. exact wislub.
  - intros d' ineqs.
    eapply islub_isleast.
    + apply pointwiselub_islubpointwise.
    + intro i. unfold pointwisefamily.
      eapply dcpomorphism_preserveslub.
      * exact isdirecv.
      * exact wislub.
      * intro j. eapply istrans_posetRelation.
        2: { exact (ineqs j). }
        apply pointwiselub_islubpointwise.
Qed.

Lemma pointwiselub_islub {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  islub F (mkdcpomorphism (pointwiselub F isdirec)
                            (pointwiselub_isdcpomorphism' F isdirec)).
Proof.
  split.
  - intro i; simpl. intro d; simpl.
    apply pointwiselub_islubpointwise.
  - intros h ineqs; simpl. intro d; simpl.
    apply pointwiselub_islubpointwise.
    intro i. use (ineqs i).
Qed.

Lemma islub_islubpointwise {D D' : dcpo} {I : UU} {g : posetofdcpomorphisms D D'}
      {F : I -> posetofdcpomorphisms D D'} (isdirec : isdirected F) :
  islub F g -> ∏ (d : D), islub (pointwisefamily F d) (pr1 g d).
Proof.
  intros islubFg d.
  set (ptlub := mkdcpomorphism (pointwiselub F isdirec)
                               (pointwiselub_isdcpomorphism' F isdirec)).
  assert (lubeq : g = ptlub).
  { apply (lubsareunique F islubFg).
    apply pointwiselub_islub. }
  rewrite lubeq.
  apply pointwiselub_islubpointwise.
Qed.

Lemma posetofdcpomorphisms_isdirectedcomplete (D D' : dcpo) :
  isdirectedcomplete (posetofdcpomorphisms D D').
Proof.
  intros I F isdirec.
  exists (mkdcpomorphism (pointwiselub F isdirec)
                         (pointwiselub_isdcpomorphism' F isdirec)).
  apply pointwiselub_islub.
Qed.

Definition dcpoofdcpomorphisms (D D' : dcpo) : dcpo.
Proof.
  eapply make_dcpo.
  - exact (posetofdcpomorphisms_isdirectedcomplete D D').
Defined.
End morphismsofdcpos_formdcpo.

(** ** Dcpos with bottom *)
Section dcpowithbottom.
Definition dcpowithbottom := ∑ (D : dcpo), ∑ (l : D), isMinimal l.
Definition dcpowithbottom_dcpo : dcpowithbottom -> dcpo := pr1.
Coercion dcpowithbottom_dcpo : dcpowithbottom >-> dcpo.
Definition dcpowithbottom_isMinimal (D : dcpowithbottom) := (pr2 (pr2 D)).
Definition dcpowithbottom_bottom (D : dcpowithbottom) := pr1 (pr2 D).

Definition dcpowithbottom_ofdcpomorphisms (D D' : dcpowithbottom) :
  dcpowithbottom.
Proof.
  exists (dcpoofdcpomorphisms D D').
  set (leastD' := dcpowithbottom_bottom D').
  set (l := mkconst_dcpomor D D' leastD').
  exists l.
  intro f. simpl. intro d.
  apply dcpowithbottom_isMinimal.
Defined.

End dcpowithbottom.

Declare Scope DCPO.
Delimit Scope DCPO with DCPO.
Local Open Scope DCPO.
Notation "A --> B" := (dcpowithbottom_ofdcpomorphisms A B) : DCPO.

(** ** The least fixed point *)
Section leastfixedpoint.

Definition iter {D : dcpowithbottom} (n : nat) (f : D --> D) : D.
Proof.
  induction n as [ | m IH].
  - exact (dcpowithbottom_bottom D).
  - apply f. exact IH.
Defined.

Lemma iter_preservesorder {D : dcpowithbottom} (f g : D --> D) :
  (f ≤ g) -> ∏ (n : nat), (iter n f ≤ iter n g).
Proof.
  intros ineq n; induction n as [ | m IH].
  - apply isrefl_posetRelation.
  - simpl. eapply istrans_posetRelation.
    + apply dcpomorphism_preservesorder. exact IH.
    + use ineq.
Qed.

(** Next, we show that each iter n is continuous, but first a small lemma.
    It could be generalised using monotone nets, c.f.
    Proposition 2.1.12 in Abramsky's and Jung's chapter "Domain Theory"
    in "Handbook of Logic in Computer Science".
    We're saying that: ⊔ f^(n+1)(⊥) = ⊔ g(⊔ f^n(⊥)), where f,g are in the
    family F.
    One inequality is easy; the other crucially relies on the fact that
    F is directed. *)
Lemma doublelubdirected {D : dcpowithbottom} {I : UU} (F : I -> D -->D)
      (isdirec : isdirected F) (n : nat) (u u' : D) :
  islub (λ i : I, iter n (F i)) u' -> islub (λ j : I, (pr1) (F j) u') u ->
  islub (λ i : I, iter (S n) (F i)) u.
Proof.
  intros islubu' islubu.
  split.
  - intro i.
    simpl. eapply istrans_posetRelation.
    + apply dcpomorphism_preservesorder.
      apply (islub_isupperbound _ islubu').
    + apply (islub_isupperbound _ islubu).
  - intros d ineqs.
    apply (islub_isleast _ islubu).
    intro i.
    set (fam := λ i : I, iter n (F i)).
    assert (isdirec' : isdirected (λ i : I, iter n (F i))).
    { split.
      - exact (isdirected_inhabited isdirec).
      - intros i1 i2.
        use factor_through_squash.
        + exact (directeduntruncated F i1 i2).
        + apply isapropishinh.
        + intro direc. apply hinhpr.
          induction direc as [k ineqs'].
          exists k.
          split.
          * apply iter_preservesorder. exact (pr1 ineqs').
          * apply iter_preservesorder. exact (pr2 ineqs').
        + apply (isdirected_order isdirec).
    }
    eapply dcpomorphism_preserveslub.
    + exact isdirec'.
    + exact islubu'.
    + intro j. simpl.
      use factor_through_squash.
      * exact (directeduntruncated F i j).
      * apply propproperty.
      * intro direc. induction direc as [k ineqs'].
        eapply istrans_posetRelation.
        -- apply dcpomorphism_preservesorder.
           apply iter_preservesorder.
           apply (pr2 ineqs').
        -- eapply istrans_posetRelation.
           ++ use (pr1 ineqs').
           ++ exact (ineqs k).
      * apply (isdirected_order isdirec).
Qed.

Lemma iter_isdcpomorphism' (D : dcpowithbottom) :
  ∏ (n : nat), isdcpomorphism' (@iter D n).
Proof.
  intros n I F isdirec g islubg.
  induction n as [| m IH].
  - split.
    + intro i. simpl. apply dcpowithbottom_isMinimal.
    + intros y ineqs. apply dcpowithbottom_isMinimal.
  - simpl. eapply doublelubdirected.
    + exact isdirec.
    + exact IH.
    + set (islub' := pointwiselub_islub F isdirec).
      set (eq := lubsareunique _ islubg islub').
      rewrite eq; cbn.
      apply pointwiselub_islubpointwise.
Qed.

(** Iter as dcpo morphism *)
Definition iter' {D : dcpowithbottom} (n : nat) : (D --> D) --> D.
Proof.
  eapply mkdcpomorphism.
  exact (iter_isdcpomorphism' D n).
Defined.

Lemma iter'_isomegachain (D : dcpowithbottom) :
  ∏ (n : nat), (@iter' D n ≤ @iter' D (S n)).
Proof.
  induction n as [ | m IH].
  - simpl. intro f. apply dcpowithbottom_isMinimal.
  - simpl. intro f. apply dcpomorphism_preservesorder. use IH.
Qed.

Lemma iter'_increases (D : dcpowithbottom) :
  ∏ (n m : nat), (n ≤ m)%nat -> (@iter' D n ≤ @iter' D m).
Proof.
  intros n m ineq.
  induction m as [ | m' IH].
  - set (nis0 := natleh0tois0 ineq).
    rewrite nis0. apply isrefl_posetRelation.
  - set (cases := natlehchoice _ _ ineq).
    induction cases as [less | equal].
    + eapply istrans_posetRelation.
      * apply IH. apply less.
      * apply iter'_isomegachain.
    + rewrite equal. apply isrefl_posetRelation.
Qed.

Lemma iter'_isdirected (D : dcpowithbottom) :
  isdirected (@iter' D).
Proof.
  split.
  - apply hinhpr. exact O.
  - intros n m. apply hinhpr. exists (n + m).
    split.
    + apply iter'_increases. apply natlehnplusnm.
    + apply iter'_increases, natlehmplusnm.
Qed.

Definition leastfixedpoint {D : dcpowithbottom} : (D --> D) --> D.
Proof.
  use mkdcpomorphism.
  - eapply pointwiselub.
    apply iter'_isdirected.
  - apply pointwiselub_isdcpomorphism'.
Defined.

Notation "'μ'" := leastfixedpoint : DCPO.

Lemma leastfixedpoint_isfixedpoint {D : dcpowithbottom} :
  ∏ (f : D --> D), (pr1 f) (pr1 μ f) = pr1 μ f.
Proof.
  intro f. unfold leastfixedpoint; cbn.
  apply isantisymm_posetRelation.
  - set (isdirec := pointwisefamily_isdirected iter' (iter'_isdirected D) f).
    eapply dcpomorphism_preserveslub.
    + exact isdirec.
    + apply pointwiselub_islubpointwise.
    + intro n. simpl.
      eapply (istrans_posetRelation _ _ (pointwisefamily iter' f (S n)) _).
      * apply isrefl_posetRelation.
      * apply pointwiselub_islubpointwise.
  - eapply (islub_isleast).
    + apply pointwiselub_islubpointwise.
    + intro n. induction n as [ | m IH].
      * apply dcpowithbottom_isMinimal.
      * unfold pointwisefamily; simpl. apply dcpomorphism_preservesorder.
        eapply istrans_posetRelation.
        -- use iter'_increases.
           ++ exact (S m).
           ++ apply natlehnsn.
        -- exact (islub_isupperbound _
                  (pointwiselub_islubpointwise iter' (iter'_isdirected D) f)
                  (S m)).
Qed.

Lemma leastfixedpoint_isleast {D : dcpowithbottom} (f : D --> D) :
  ∏ (d : D), ((pr1 f) d ≤ d) -> (pr1 μ f ≤ d).
Proof.
  intros d ineq.
  eapply islub_isleast.
  - apply pointwiselub_islubpointwise.
  - intro n; induction n as [ | m IH].
    + apply dcpowithbottom_isMinimal.
    + unfold pointwisefamily. simpl.
      eapply istrans_posetRelation.
      * apply dcpomorphism_preservesorder. exact IH.
      * exact ineq.
Qed.

Close Scope DCPO.

End leastfixedpoint.
