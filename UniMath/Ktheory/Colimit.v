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

Definition Limit {C I:Precategory} (D: I==>C) := Representation (cone_functor D).

Definition Colimit {C I:Precategory} (D: I==>C) := Representation (cocone_functor D).

Definition pr_ {C I:Precategory} {D: I==>C} (lim:Limit D) (i:I) : universalObject lim → D i.
Proof. intros. exact ((pr1 (universalElement lim) i)). Defined.

Definition in_ {C I:Precategory} {D: I==>C} (colim:Colimit D) (i:I) : D i → universalObject colim.
Proof. intros. exact ((pr1 (universalElement colim) i)). Defined.

Definition pr_comm {C I:Precategory} {D: I==>C} (lim:Limit D) {i j:I} (f:i→j) :
  # D f ∘ pr_ lim i = pr_ lim j.
Proof. intros. exact (pr2 (universalElement lim) _ _ f). Defined.

Definition in_comm {C I:Precategory} {D: I==>C} (colim:Colimit D) {i j:I} (f:i→j) :
  in_ colim j ∘ # D f = in_ colim i.
Proof. intros. exact (pr2 (universalElement colim) _ _ f). Defined.

Definition hasLimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Limit D.

Definition hasColimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Colimit D.

Definition lim_functor (C:Precategory) (lim:hasLimits C) (I:Precategory) :
  [I,C] ==> C
  := universalObjectFunctor C
   □ addStructure cone_functor (lim I).

Definition colim_functor (C:Precategory) (colim:hasColimits C) (I:Precategory) :
  [I,C] ==> C
  := functor_rm_op (
         universalObjectFunctor C^op
       □ addStructure cocone_functor (colim I)).

Theorem functorPrecategoryLimits (A B:Precategory) : hasLimits B -> hasLimits [A,B].
Proof.
Abort.

Theorem functorPrecategoryColimits (A B:Precategory) : hasColimits B -> hasColimits [A,B].
Proof.
Abort.


(*
Local Variables:
compile-command: "make -C ../.. TAGS TAGS-Ktheory UniMath/Ktheory/DiagramColimit.vo"
End:
*)
