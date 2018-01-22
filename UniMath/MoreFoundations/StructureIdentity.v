(** * Structure identity *)

Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Tactics.
Require Export UniMath.MoreFoundations.AlternativeProofs.

Section StructureIdentity.

  (** ** abstract the proof of Poset_rect for use in multiple situations *)

  (** See Section 9.8 of the HoTT book, on "The structure identity principle". *)

  Open Scope poset.

  Context {Base : UU}                              (* base type *)
          (Data : Base -> Poset).                  (* the additional structure *)

  Definition Struc := ∑ b, Data b.   (* the structures *)

  (** for example: Base = hSet, Data = PartialOrder, Struc = Poset *)

  Local Definition DataEquiv (b:Base) (d d':Data b) := d ≤ d' ∧ d' ≤ d.

  Local Definition StrucEquiv (X Y:Struc)
    := ∑ (p: pr1 X = pr1 Y), DataEquiv _ (transportf Data p (pr2 X)) (pr2 Y).

  Notation "X ≅ Y" := (StrucEquiv X Y).

  Theorem Struc_univalence (X Y:Struc) : X=Y ≃ X≅Y.
  Proof.
    simple refine (@remakeweq _ _ _ _ _).
    { intermediate_weq (X╝Y).
      { apply total2_paths_equiv'. }
      { use weqfibtototal; intro p. apply weqimplimpl.
        { intros q. split; induction q; apply isrefl_posetRelation. }
        { intros e. apply isantisymm_posetRelation.
          - exact (pr1 e).
          - exact (pr2 e). }
        { apply (setproperty (Data _)). }
        { apply (propproperty (DataEquiv _ _ _)). } } }
    { intros e. induction e. exists (idpath _). split; apply isrefl_posetRelation. }
    try reflexivity.            (* fails, which is why we are using "remakeweq" here *)
    intro e. now induction e.
  Defined.

  Theorem Equiv_rect (X Y : Struc) (P : X ≅ Y -> UU) :
    (∏ e : X = Y, P (Struc_univalence _ _ e)) -> ∏ f, P f.
  Proof.
    intros ih f.
    set (p := ih (invmap (Struc_univalence _ _) f)).
    set (h := homotweqinvweq (Struc_univalence _ _) f).
    exact (transportf P h p).
  Defined.

  (* Ltac Struc_induction f e := generalize f; apply Equiv_rect; intro e; clear f. *)

End StructureIdentity.
