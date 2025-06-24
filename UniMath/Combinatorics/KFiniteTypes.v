

  (********************************************************************)
  (* * Kuratowski finite types                                        *)
  (*                                                                  *)
  (* [kfinstruct] -- A Kuratowski structure on a type X consists of a *)
  (*                 natural number n : ℕ and a surjective function   *)
  (*                         f : ⟦ n ⟧ → X.                           *)
  (*                                                                  *)
  (* [iskfinite] -- A type X is Kuratowski finite (K-finite) if there *)
  (*                merely exists some Kuratowski structure on X:     *)
  (*                        iskfinite X := ∥ kfinstruct X ∥.          *)
  (*                                                                  *)
  (********************************************************************)

(*
        Contents
        1. Kuratowski structure.
        2. Examples of K-structures.
        3. K-finite types.
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.DecidablePropositions.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope stn.

Section kuratowski_structure.
  (**
   1. Kuratowski structure on types.
   *)
  Definition kfinstruct (X : UU) : UU
    := ∑ (n : nat)
         (f : ⟦ n ⟧ → X),
      issurjective f.

  (* Constructor. *)
  Definition make_kfinstruct {X : UU}
    (n : nat)
    (f : ⟦ n ⟧ -> X)
    (fsurjective : issurjective f)
    : kfinstruct X
    := (n ,, f ,, fsurjective).

  (* Accessors. *)
  Definition kfinstruct_cardinality {X : UU} (f : kfinstruct X) : nat
    := pr1 f.

  Definition kfinstruct_map {X : UU} (f : kfinstruct X)
    : ⟦ kfinstruct_cardinality f ⟧ -> X
    := pr12 f.
  Coercion kfinstruct_map : kfinstruct >-> Funclass.

  Definition issurjective_kfinstruct {X : UU}
    (f : kfinstruct X) : issurjective f
    := pr22 f.

  (* Some functions useful for constructing kfinstruct from different data. *)
  Definition kfinstruct_from_surjection {X Y : UU}
    (g : X → Y)
    (gsurjective : issurjective g)
    : kfinstruct X → kfinstruct Y.
  Proof.
    intros f.
    use make_kfinstruct.
    - exact(kfinstruct_cardinality f).
    - exact(g ∘ f).
    - apply issurjcomp.
      apply issurjective_kfinstruct.
      exact gsurjective.
  Defined.

  Definition kfinstruct_weqf {X Y : UU}
    (w : X ≃ Y) : kfinstruct X → kfinstruct Y.
  Proof.
    apply(kfinstruct_from_surjection w).
    apply issurjectiveweq.
    apply weqproperty.
  Defined.

  Definition kfinstruct_weqb {X Y : UU}
    (w : X ≃ Y) : kfinstruct Y → kfinstruct X.
  Proof.
    apply(kfinstruct_from_surjection (invmap w)).
    apply issurjectiveweq.
    apply isweqinvmap.
  Defined.

  Definition kfinstruct_contr {X : UU}
    (contr : iscontr X)
    : kfinstruct X.
  Proof.
    use(make_kfinstruct 1).
    - exact(λ _, iscontrpr1 contr).
    - apply issurjective_to_contr, contr.
      exact(● 0).
  Defined.

  Definition kfinstruct_coprod {X Y : UU}
    : kfinstruct X → kfinstruct Y → kfinstruct (X ⨿ Y).
  Proof.
    intros f g.
    set (n := kfinstruct_cardinality f).
    set (m := kfinstruct_cardinality g).
    use make_kfinstruct.
    - exact(n + m).
    - exact((coprodf f g) ∘ invweq (weqfromcoprodofstn n m)).
    - apply issurjcomp.
      + apply issurjectiveweq.
        apply weqproperty.
      + apply issurjective_coprodf
        ; apply issurjective_kfinstruct.
  Defined.

  Definition kfinstruct_dirprod {X Y : UU}
    : kfinstruct X -> kfinstruct Y -> kfinstruct (X × Y).
  Proof.
    intros f g.
    set (k := kfinstruct_cardinality f).
    set (l := kfinstruct_cardinality g).

    use make_kfinstruct.
    - exact(k * l).
    - exact((dirprodf f g) ∘ (invweq (weqfromprodofstn k l))).
    - apply issurjcomp.
      + apply issurjectiveweq, weqproperty.
      + apply issurjective_dirprodf
        ; apply issurjective_kfinstruct.
  Defined.

  (* This relates [kfinstruct] to [finstruct]. *)
  Definition kfinstruct_finstruct {X : UU} : finstruct X → kfinstruct X.
  Proof.
    intros finstr.
    use make_kfinstruct.
    - apply finstr.             (* n : nat *)
    - apply finstr.             (* ⟦ n ⟧ ≃ X *)
    - apply issurjectiveweq.
      apply weqproperty.
  Defined.

End kuratowski_structure.

Section kstructure_examples.
  (**
   2. Examples of types with K-structure.
   *)

  Definition kfinstruct_unit : kfinstruct unit.
  Proof.
    apply kfinstruct_contr.
    apply iscontrunit.
  Defined.

  Definition kfinstruct_bool : kfinstruct bool.
  Proof.
    use(make_kfinstruct 2).
    - exact(two_rec false true).
    - red; apply bool_rect; apply hinhpr.
      + exists (● 1); exact(idpath _).
      + exists (● 0); exact(idpath _).
  Defined.

  Definition kfinstruct_stn (n : nat) : kfinstruct (⟦ n ⟧).
  Proof.
    use make_kfinstruct.
    - exact n.
    - exact(idfun (⟦ n ⟧)).
    - exact(issurjective_idfun (⟦ n ⟧)).
  Defined.

  Definition kfinstruct_stn_indexed {n : nat}
    (P : ⟦ n ⟧ → UU)
    (index : ∏ (k : ⟦ n ⟧), kfinstruct (P k))
    : kfinstruct (∑ (k : ⟦ n ⟧), P k).
  Proof.
    set (J := λ (j : ⟦ n ⟧), kfinstruct_cardinality (index j)).

    use(kfinstruct_from_surjection (X:=∑ (k : ⟦n⟧), ⟦J k⟧)).
    - apply totalfun, index.
    - apply issurjective_totalfun.
      intro; apply issurjective_kfinstruct.
    - apply(kfinstruct_weqb (weqstnsum1 J)).
      apply kfinstruct_stn.
  Defined.

End kstructure_examples.

Section kfinite_definition.
  (**
   3. The property of being K-finite.

      A type is Kuratowski finite if it merely admits a K-structure.
   *)

  Definition iskfinite (X : UU) : UU
    := ∥ kfinstruct X ∥.

  Definition kfinstruct_iskfinite {X : UU} : kfinstruct X → iskfinite X
    := hinhpr.

  Definition iskfinite_weqf {X Y : UU} (w : X ≃ Y)
    : iskfinite X → iskfinite Y
    := hinhfun (kfinstruct_weqf w).

  Definition iskfinite_weqb {X Y : UU} (w : X ≃ Y)
    : iskfinite Y → iskfinite X
    := hinhfun (kfinstruct_weqb w).

  Definition iskfinite_from_surjection {X Y : UU}
    (f : X → Y)
    (fsurjective : issurjective f)
    : iskfinite X → iskfinite Y
    := hinhfun (kfinstruct_from_surjection f fsurjective).

  Definition iskfinite_unit : iskfinite unit
    := hinhpr kfinstruct_unit.

  Definition iskfinite_bool : iskfinite bool
    := hinhpr kfinstruct_bool.

  Definition iskfinite_contr (X : UU) (Xcontr : iscontr X) : iskfinite X
    := hinhpr (kfinstruct_contr Xcontr).

  Definition iskfinite_coprod {X Y : UU}
    : iskfinite X → iskfinite Y → iskfinite (X ⨿ Y)
    := hinhfun2
         kfinstruct_coprod.

  Definition iskfinite_dirprod {X Y : UU}
    : iskfinite X → iskfinite Y → iskfinite (X × Y)
    := hinhfun2
         kfinstruct_dirprod.

  (* Any Bishop-finite type is also K-finite. *)
  Definition iskfinite_isfinite {X : UU}
    : isfinite X → iskfinite X
    := hinhfun kfinstruct_finstruct.

End kfinite_definition.

Section iskfinite_isdeceq_isfinite.
(** 
  This section provides the necessary construction to prove that 
  every K-Finite type with decidable equality is Bishop-finite. 
  
  Proof outline: 
  Let X be a K-Finite type. Then there exists n : nat with a surjection 
  from stn n to X.

  The proof goes by induction on n, with the type X being generalized.
  In the base case, we have a surjection from an uninhabited type to X.
  Thus, X must also have no elements and therefore, X is equivalent with 
  stn 0.

  In the inductive step, we assume that for any type X for which there 
  exists a surjection from stn n to X and has decidable equality is 
  Bishop finite. We have to show that if there exists a surjection f 
  from stn (S n) to X and X has decidable equality, then X is Bishop 
  finite.
  Let g : stn n -> X such that g (x) := f x. If X has decidable equality, 
  then it is decidable whether f (n) is included in the image of g. 

  We will thus proceed by case analysis on whether f n is included in the image of g.
  If f n is included in the image of g, then g must be a surjection as well. By the inductive 
  hypothesis X is Bishop finite. If f n is not included in the image of g, we will denote 
  y := f n. We now consider the type X / y (pair X (\x -> x != y)) which is inhabited by 
  terms different than y. First, we note that X / y has decidable equality. Secondly, we note 
  that X / y + unit is equivalent to X. Lastly, we note that by restricting the codomain of g 
  to X / y, we obtain a surjection g1 : stn n -> X / y. By the inductive hypothesis, the type 
  X / y is Bishop finite, and thus equivalent to stn m for some m : nat. 
  To conclude, we have the following chain of equivalences 
  X <-> X / y + 1 <-> stn m + 1 <-> stn (S m). Thus, X is Bishop finite.

  *)
  Definition removeterm {X : UU} (y : X) : X → UU := λ x, x != y.

  Lemma isPredicateremoveterm {X : UU} (y : X) : isPredicate (removeterm y).
  Proof.
    intros x. apply isapropneg.
  Qed.

  Lemma removetermequiv {X : UU} (y : X) : isdeceq X → (∑ (x : X), ¬ (x = y)) ⨿ unit ≃ X.
  Proof.
    intros deceqx.
    use weq_iso.
    - intros [[x neq] | tt]; [apply x | apply y].
    - intros x. induction (deceqx x y); [right; apply tt | left].
      apply tpair with (pr1 := x), b. 
    - intros [[x neq] | tt].
      + induction (deceqx x y).
        * apply fromempty, neq, a.
        * simpl. apply maponpaths, subtypePath; 
          [apply isPredicateremoveterm | apply idpath].
      + induction (deceqx y y).
        * induction tt. apply idpath.
        * apply fromempty, b, idpath.
    - intros x; cbn beta.
      induction (deceqx x y); simpl;
      try induction a; apply idpath.
  Qed.

  Lemma issurjective_stnfun_excludefixed {X : UU} {n : nat} (f : stn (S n) → X) 
        (nfib : ¬ hfiber (fun_stnsn_to_stnn f) (f lastelement)) : issurjective f → 
        issurjective (stnfun_excludefixed f nfib).
  Proof.
    intros surjf y.
    destruct y as [x neq].
    use squash_to_prop.
    - exact (hfiber f x).
    - exact (surjf x).
    - apply propproperty.
    - intros [[m lth] q]; clear surjf. apply hinhpr.
      induction (natlehchoice _ _ (natlthsntoleh _ _ lth)).
      + apply (tpair _ (m ,, a)).
        unfold stnfun_excludefixed, fun_stnsn_to_stnn, make_stn.
        apply subtypePath; try (apply isPredicateremoveterm); simpl.
        induction q. apply maponpaths, stn_eq, idpath. 
      + assert (m ,, lth = lastelement) by apply stn_eq, b.
        apply fromempty, neq. induction X0. apply pathsinv0, q.
  Qed.

  Lemma kfinstruct_dec_finstruct {X : UU} : isdeceq X → kfinstruct X → finstruct X.
  Proof.
    intros deceqX [n [f surj]].
    generalize dependent X.
    induction n; intros.
    - apply tpair with (pr1 := 0).
      apply surjfromstn0toneg with (f := f). assumption. 
    - set (g := fun_stnsn_to_stnn f).
      set (y := f lastelement).
      induction (isdeceq_isdecsurj g y deceqX).
      + apply IHn with (f := g); try apply surj_fun_stnsn_to_stnn; assumption.
      + set (g' := stnfun_excludefixed f b).
        set (surjg' := (issurjective_stnfun_excludefixed f b surj)).
        specialize IHn with (f := g').
        apply IHn in surjg'; 
        [ | apply isdeceq_subtype; try assumption; intros x; apply isapropneg ].
        destruct surjg' as [s1 s2].
        apply tpair with (pr1 := (S s1)); unfold nelstruct.
        eapply weqcomp. 
        * apply invweq, weqdnicoprod, lastelement.
        * eapply weqcomp. 
          { eapply weqcoprodf1, s2. }
          apply removetermequiv; assumption.
  Qed.

  Lemma iskfinitedectoisfinite {X : UU} : isdeceq X → iskfinite X → isfinite X.
  Proof.
    intros deceqX. apply hinhfun, kfinstruct_dec_finstruct, deceqX.
  Qed.
End iskfinite_isdeceq_isfinite.