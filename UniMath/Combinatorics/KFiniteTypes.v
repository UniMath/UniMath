

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
