
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Combinatorics.KFiniteTypes.

(** * Kfinite Subtypes

    Some results on K-finite subtypes.

    [iskfinite_singleton] - Singletons are K-finite.
    [iskfinite_union] - A union of (Bishop-) finitely many K-finite subtypes is K-finite.

    [kfinite_subtype] - Definition of subtypes that are K-finite.

 *)

Section kfinite_subtypes.
  Local Open Scope stn.
  Local Open Scope subtype.

  (* Singletons are always K-finite. *)
  Lemma iskfinite_singleton {X : UU} (x : X)
    : iskfinite (singleton x).
  Proof.
    apply kfinstruct_iskfinite.
    use(make_kfinstruct 1).
    - exact(λ (_ : ⟦ 1 ⟧), (x ,, hinhpr (idpath x))).
    - intros [z xz].
      use(hinhfun _ xz); intro.
      use(make_hfiber _ (stnpr 0)).
      now apply subtypePath_prop.
  Qed.

  (* [indexed_carrier_to_carrier_union] and [reindex_carrier_union] need
     better names, and possibly be moved somewhere else
     (MoreFoundations/Subtypes.v?), they are currently only used to help
     prove that K-finite unions are K-finite. *)
  Definition indexed_carrier_to_carrier_union
    {X I : UU}
    (index : I → hsubtype X)
    : (∑ (i : I), (carrier (index i))) → (carrier (⋃ index)).
  Proof.
    intro h.                   (* This is not very pretty. *)
    exact(pr12 h ,, hinhpr (pr1 h ,, pr22 h)).
  Defined.

  Lemma issurjective_indexed_carrier_to_union
    {X I : UU}
    (index : I → hsubtype X)
    : issurjective (indexed_carrier_to_carrier_union index).
  Proof.
    intros [x in_union]. (* x ∈ ⋃ index *)
    use(hinhfun _ in_union).
    intros [i in_index]. (* ∑ (i : I), index i x *)
    use make_hfiber.
    - exact(i ,, x ,, in_index). (* ∑ (i : I), (carrier (index i)) *)
    - now apply subtypePath_prop.
  Qed.

  Definition reindex_carrier_union
    {X : UU}
    {I J : UU}
    (index : I → hsubtype X)
    (g : J → I)
    : (carrier (⋃ (index ∘ g))) → (carrier (⋃ index)).
  Proof.
    apply subtype_inc; intro.
    use hinhfun.
    use(fpmap g).
  Defined.

  Lemma issurjective_reindex_carrier_union
    {X I J : UU}
    (index : I → hsubtype X)
    (g : J → I)
    (gsurjective : issurjective g)
    : issurjective (reindex_carrier_union index g).
  Proof.
    intros [x in_union].      (* x ∈ (⋃ index) *)
    use(hinhfun _ in_union).
    intros [i index_ix].
    use make_hfiber.
    - exists x.
      use(hinhfun _ (gsurjective i)).
      intros [j jpath].
      exists j.
      refine(transportb _ (eqtohomot _ x) index_ix).
      exact(maponpaths index jpath).
    - now apply subtypePath_prop.
  Qed.

  (* The union of K-finitely many K-finite subtypes is K-finite. *)
  Definition kfinstruct_union
    {I X : UU}
    (index : I → hsubtype X)
    (g : kfinstruct I)
    (index_finite : ∏ (i : I), kfinstruct (index i))
    : kfinstruct (⋃ index).
  Proof.
    (* (⋃ idx ∘ g) → ⋃ idx *)
    apply(kfinstruct_from_surjection (reindex_carrier_union index g)).
    apply issurjective_reindex_carrier_union.
    apply issurjective_kfinstruct.

    (* (∑(k : ⟦ n ⟧), (idx (g k))) → ⋃ (idx ∘ g) *)
    apply(kfinstruct_from_surjection (indexed_carrier_to_carrier_union (index ∘ g))).
    apply issurjective_indexed_carrier_to_union.

    apply kfinstruct_stn_indexed.
    intro; apply index_finite.
  Defined.

  (* The union of (Bishop)-finitely many K-finite subtypes is K-finite. *)
  Lemma iskfinite_union
    {I X : UU}
    (index : I → hsubtype X)
    (Ifinite : isfinite I)
    (index_finite : ∏ (i : I), iskfinite (index i))
    : iskfinite (⋃ index).
  Proof.
    assert(finitechoicebase : ∥ ∏ (i : I), kfinstruct (index i) ∥). {
      use ischoicebasefiniteset.
      apply Ifinite.
      apply index_finite.
    }
    use(hinhfun2 _ Ifinite finitechoicebase).
    intro; apply kfinstruct_union.
    now apply kfinstruct_finstruct.
  Qed.

  (* In particular a binary union of K-finite subtypes is K-finite. *)
  Lemma iskfinite_binary_union {X : UU}
    (A B : hsubtype X)
    (afinite : iskfinite A)
    (bfinite : iskfinite B)
    : iskfinite (A ∪ B).
  Proof.
    (* We could use iskfinite_union defined above, but we opt to
       give a direct proof instead by constructing a sequence of
       surjective maps

       ⟦ n + m ⟧ -~> ⟦ n ⟧ ⨿ ⟦ m ⟧ --> A ⨿ B --> carrier (A ∪ B).
     *)
    use(hinhfun2 _ afinite bfinite).
    intros afinstruct bfinstruct.
    use make_kfinstruct.

    - exact(kfinstruct_cardinality afinstruct +
              kfinstruct_cardinality bfinstruct).
    - refine(coprod_carrier_binary_union A B ∘ _).
      refine(coprodf afinstruct bfinstruct ∘ _).
      apply weqfromcoprodofstn.
    - apply issurjcomp.
      apply issurjcomp.

      * apply issurjectiveweq, isweqinvmap.
      * apply issurjective_coprodf; apply issurjective_kfinstruct.
      * exact(issurjective_coprod_carrier_binary_union A B).
  Qed.

  (* Sometimes it's better to bundle it together. *)

  Definition kfinite_subtype (X : UU) : UU
    := ∑ (A : hsubtype X),
      iskfinite (carrier A).

  Definition subtype_from_kfinite_subtype {X}
    : kfinite_subtype X -> hsubtype X
    := pr1.
  Coercion subtype_from_kfinite_subtype : kfinite_subtype >-> hsubtype.

  Definition kfinite_subtype_property {X}
    (A : kfinite_subtype X)
    : iskfinite (carrier A)
    := pr2 A.

  Definition make_kfinite_subtype {X : UU}
    (A : hsubtype X)
    (finite_carrier : iskfinite (carrier A))
    : kfinite_subtype X
    := (A ,, finite_carrier).

  Definition kfinite_subtype_union {X I : UU}
    (index : I -> kfinite_subtype X)
    (index_finite : isfinite I)
    : kfinite_subtype X.
  Proof.
    use make_kfinite_subtype.
    - exact(subtype_union index).
    - abstract(apply(iskfinite_union index index_finite);
               intro; apply kfinite_subtype_property).
  Defined.

  Definition kfinite_subtype_singleton {X : UU}
    (x : X) : kfinite_subtype X.
  Proof.
    use make_kfinite_subtype.
    - exact(singleton x).
    - exact(iskfinite_singleton x).
  Defined.
End kfinite_subtypes.
