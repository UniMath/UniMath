Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Cocone
        UniMath.Ktheory.Bifunctor
        UniMath.CategoryTheory.colimits.colimits.

Set Automatic Introduction.

Local Open Scope cat.

Definition Colimit {C I:Precategory} (D: I==>C) := Representation (cocone_functor D).

Definition colimitObject {C I:Precategory} {D: I==>C} (colim:Colimit D) : ob C
  := universalObject colim.

Coercion colimitObject : Colimit >-> ob.

Definition colimitCocone {C I:Precategory} {D: I==>C} (colim:Colimit D) : cocone' D colim
  := universalElement colim.

Coercion colimitCocone : Colimit >-> cocone'.

Definition colimitIn {C I:Precategory} {D: I==>C} (colim:Colimit D) (i:I) : D i → colim.
Proof. intros. exact (colim i). Defined.

Definition colimitInTriangle {C I:Precategory} {D: I==>C} (colim:Colimit D) {i j:I} (f:i→j) :
  colimitIn colim j ∘ # D f = colimitIn colim i.
Proof. intros. exact (coconeInCommutes colim i j f). Defined.

Definition hasColimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Colimit D.

Definition colim_functor (C:Precategory) (colim:hasColimits C) (I:Precategory) : [I,C] ==> C.
Proof.
  unfold hasColimits in colim.
  refine (_,,_).
  - refine (_,,_).
    + exact (colim _).
    + intros D D' p; simpl.
      (* apply universalObjectFunctor. *)
      (* now apply (# cocone_functor). *)
      admit.
  - split.
    + intro D. simpl.
      (* refine (_ @ objectMapIdentity (colim I D)). *)
      (* apply maponpaths. apply subtypeEquality. *)
      (* { intro p; simpl in p. apply isaprop_is_nat_trans, homset_property. } *)
      (* { simpl. apply funextsec; intro c. *)
      (*   apply funextsec; intro φ. *)
      (*   refine (total2_paths _ _). *)
      (*   { simpl. apply funextsec; intro i. exact (id_left _). } *)
      (*   { apply funextsec; intro i; apply funextsec; intro j; apply funextsec; intro e. *)
      (*     apply homset_property. } } *)
      admit.
    + intros D D' D'' p q.


      (* refine (functor_comp _ _ _ _ p q). *)



Abort.

Definition diagram_eval {A B I:Precategory} : I ==> [A, B] -> A -> I ==> B.
Proof.
  intros D a. refine (_,,_).
  - refine (_,,_).
    + intro i. exact ((D i : _ ==> _) a).
    + simpl. intros i j e. exact ((# D e : _ ⟶ _) a).
  - split.
    + intro i; simpl.
      exact (maponpaths (λ F : _⟶_, F _) (functor_id D _)).
    + intros i j k f g; simpl.
      exact (maponpaths (λ F : _⟶_, F _) (functor_comp D _ _ _ _ _)).
Defined.

Theorem functorPrecategoryColimits (A B:Precategory) : hasColimits B -> hasColimits [A,B].
Proof.
  intros colim ? ?.
  unfold Colimit. unfold Representation.
  set (D' := bifunctor_comm D).
  - refine (_,,_).
    + refine (_,,_).
      * refine (_,,_).
        { intro a. exact (colimitObject (colim I (diagram_eval D a))). }
        { intros a a' f; simpl.
      (*   { simpl. intros a a' f. apply diagram_map_on_colim. *)
      (*     apply diagram_eval_map. exact f. } *)
      (* * split. *)
      (*   { intro a; simpl. *)
      (*     refine (_ @ Representation.objectMapIdentity _). *)
      (*     unfold diagram_map_on_colim. *)
      (*     apply maponpaths. *)
      (*     rewrite diagram_eval_map_on_identity. *)
      (*     apply diagram_map_on_diagram_identity_map. } *)
      (*   { intros a a' a'' f g. simpl. *)

Abort.


(*
Local Variables:
compile-command: "make -C ../.. TAGS TAGS-Ktheory UniMath/Ktheory/DiagramColimit.vo"
End:
*)
