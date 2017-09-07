Require Export UniMath.MoreFoundations.Notations.

Definition Subposet (X:Poset) := hsubtype X. (* this seems simpler than the next one *)

Definition Subposet' (X:Poset) := ∑ (S:Poset) (f:posetmorphism S X), isincl f.

Definition Subposet'_to_Poset {X:Poset} (S:Subposet' X) := pr1 S.

Coercion Subposet'_to_Poset : Subposet' >-> Poset.

Definition Subposet_to_Subposet' {X:Poset} : Subposet X -> Subposet' X.
Proof.
  intros S. use tpair.
  - exists (carrier_subset S).
    use tpair.
    + intros s t. exact (pr1 s ≤ pr1 t)%poset.
    + simpl. split.
      { split.
        { intros s t u. exact (istrans_posetRelation _ _ _ _). }
        { intros s. exact (isrefl_posetRelation _ _). } }
      { intros s t a b. apply subtypeEquality_prop. exact (isantisymm_posetRelation _ _ _ a b). }
  - simpl. use tpair.
    + exists (pr1carrier _).
      intros s t a. simpl in s,t. exact a.
    + simpl. apply isinclpr1carrier.
Defined.

Definition Subposet'_to_Subposet {X:Poset} : Subposet' X -> Subposet X.
Proof.
  intros S x. set (f := pr1 (pr2 S)); simpl in f. exact (nonempty (hfiber f x)).
Defined.

Coercion Subposet_to_Subposet' : Subposet >-> Subposet'.

Definition Subposet'_equiv_Subposet (X:Poset) : Subposet' X ≃ Subposet X.
Proof.
  exists Subposet'_to_Subposet.
  apply set_bijection_to_weq.
  - split.
    + intros S.
      exists (Subposet_to_Subposet' S).
      apply funextfun; intro z.
      apply hPropUnivalence.
      * simple refine (hinhuniv _); intro w.
        simpl in w. induction w as [s p]. induction s as [y q]; simpl in p.
        induction p. exact q.
      * intro h. apply hinhpr. exists (z,,h). reflexivity.
    + intros S T p.
      (* first develop univalence for posets and Poset_rect *)
      admit.
  - unfold Subposet.
    apply isasethsubtype.
Abort.
