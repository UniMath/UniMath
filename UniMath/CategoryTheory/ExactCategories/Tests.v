(** Exact category prerequisite tests *)

Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.Monics.
Require Export UniMath.CategoryTheory.Epis.
Require Export UniMath.CategoryTheory.limits.zero.
Require Export UniMath.CategoryTheory.limits.kernels.
Require Export UniMath.CategoryTheory.limits.cokernels.
Require Export UniMath.CategoryTheory.limits.binproducts.
Require Export UniMath.CategoryTheory.limits.bincoproducts.
Require Export UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.CategoryTheory.limits.pushouts.
Require Export UniMath.CategoryTheory.limits.BinDirectSums.
Require Export UniMath.CategoryTheory.limits.Opp.
Require Export UniMath.CategoryTheory.CategoriesWithBinOps.
Require Export UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Export UniMath.CategoryTheory.PreAdditive.
Require Export UniMath.CategoryTheory.Morphisms.
Require Export UniMath.CategoryTheory.Additive.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.Subcategory.Full.
Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.PartA.
Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.Algebra.BinaryOperations.
Require Export UniMath.Algebra.Monoids_and_Groups.
Import AddNotation.
Local Open Scope addmonoid.
Local Open Scope abgr.
Local Open Scope logic.
Local Open Scope cat.
Local Arguments isZero {_} _.
Local Arguments BinDirectSumOb {_ _ _}.
Local Arguments to_binop {_ _ _}.
Local Arguments grinv {_}.
Local Arguments BinDirectSum {_}.
Local Arguments to_Pr1 {_ _ _} _.
Local Arguments to_Pr2 {_ _ _} _.
Local Arguments to_In1 {_ _ _} _.
Local Arguments to_In2 {_ _ _} _.
Local Arguments to_BinOpId {_ _ _ _ _ _ _ _}.
Local Arguments to_IdIn1 {_ _ _ _ _ _ _ _}.
Local Arguments to_IdIn2 {_ _ _ _ _ _ _ _}.
Local Arguments to_Unel1 {_ _ _ _ _ _ _ _}.
Local Arguments to_Unel2 {_ _ _ _ _ _ _ _}.
Local Arguments MorphismPair : clear implicits.
Local Arguments morphism_from_iso {_ _ _}.
Local Arguments ToBinDirectSum {_ _ _} _ {_}.
Local Arguments isBinDirectSum {_ _ _ _}.

Require Import UniMath.CategoryTheory.ExactCategories.ExactCategories.

Goal ∏ (C:precategory) (a b:C) (f: a --> b), isMonic (C:=C) f = isEpi (C:=C^op) f.
  reflexivity.
Defined.
Goal ∏ (C:precategory) (a b:C) (f: a --> b), isEpi (C:=C) f = isMonic (C:=C^op) f.
  reflexivity.
Defined.
(** Here's why we prefer to use z_iso instead of iso : *)
Goal ∏ (C:precategory) (a b:C) (f:z_iso a b), z_iso_inv (z_iso_inv f) = f.
  reflexivity.
Defined.
Goal ∏ (C:precategory) (a b:C) (f:z_iso (C:=C) a b), opp_z_iso (opp_z_iso f) = f.
  reflexivity.
Defined.
Goal ∏ (C:precategory) (a b:C) (f:z_iso (C:=C^op) b a), opp_z_iso (opp_z_iso f) = f.
  reflexivity.
Defined.
Goal ∏ (M : precategory) {X:Type} (j : X -> ob M),
  induced_precategory M^op j = (induced_precategory M j)^op.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:precategory) (P:MorphismPair M), MorphismPair_opp (MorphismPair_opp P) = P.
Proof.
  reflexivity.
Qed.
Goal ∏ {M : precategory} (A B C:M) (f : A --> C) (g : B --> C), Pullback f g = Pushout (C:=M^op) f g.
  reflexivity.
Defined.
Goal ∏ {M : precategory} (A B C:M) (f : A --> C) (g : A --> C), Pushout f g = Pullback (C:=M^op) f g.
  reflexivity.
Defined.
Goal ∏ (M : precategoryWithBinOps), oppositePrecategoryWithBinOps (oppositePrecategoryWithBinOps M) = M.
Proof.
  reflexivity.
Defined.
Goal ∏ {M:precategoryWithBinOps} {X:Type} (j : X -> ob M),
  oppositePrecategoryWithBinOps (induced_precategoryWithBinOps M j) =
  induced_precategoryWithBinOps (oppositePrecategoryWithBinOps M) j.
Proof.
  reflexivity.           (* 0.038 secs *)
Qed.
Goal ∏ (M : categoryWithAbgrops), oppositeCategoryWithAbgrops (oppositeCategoryWithAbgrops M) = M.
Proof.
  reflexivity.
Defined.
Goal ∏ {M:categoryWithAbgrops} {X:Type} (j : X -> ob M),
  oppositeCategoryWithAbgrops (induced_categoryWithAbgrops M j) =
  induced_categoryWithAbgrops (oppositeCategoryWithAbgrops M) j.
Proof.
  reflexivity.           (* 0.183 secs *)
Qed.
Goal ∏ (M : PreAdditive), oppositePreAdditive (oppositePreAdditive M) = M.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:PreAdditive) (x y:M) (xy : BinDirectSum x y),
  oppositeBinDirectSum (M:=oppositePreAdditive M) (oppositeBinDirectSum xy) = xy.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:PreAdditive) (A B:M) (AB : BinDirectSum A B), reverseBinDirectSum (oppositeBinDirectSum AB) = oppositeBinDirectSum (reverseBinDirectSum AB).
  reflexivity.
Defined.
Goal ∏ (M:PreAdditive) (A B:M) (AB : BinDirectSum A B), reverseBinDirectSum (reverseBinDirectSum AB) = AB.
  Fail reflexivity.
Abort.

Local Definition hom (C:precategory_data) : ob C -> ob C -> UU := λ c c', precategory_morphisms c c'.
Local Definition Hom (C : category) : ob C -> ob C -> hSet := λ c c', hSetpair _ (homset_property C c c').
Local Definition Hom_add (C : PreAdditive) : ob C -> ob C -> abgr := λ c c', (@to_abgr C c c').

Section Sanity.
  Context (M : category) (x y:M) (f : hom M x y) (g : Hom M x y).
  Goal Hom M x y. exact f. Defined.
  Goal hom M x y. exact g. Defined.
End Sanity.

Section Sanity2.
  Context (M : PreAdditive) (x y:M) (f : hom M x y) (g : Hom M x y) (h : Hom_add M x y).
  Goal Hom_add M x y. exact f. Defined.
  Goal Hom_add M x y. exact g. Defined.
  Goal Hom M x y. exact f. Defined.
  Goal Hom M x y. exact h. Defined.
  Goal hom M x y. exact g. Defined.
  Goal hom M x y. exact h. Defined.
End Sanity2.

Goal ∏ (M:precategory) (P:MorphismPair M), MorphismPair_opp (MorphismPair_opp P) = P.
Proof.
  reflexivity.
Qed.
Goal ∏ (M:precategory) (p:MorphismPair (M^op)), MorphismPair M.
  intros. exact (MorphismPair_opp p).
Qed.
Goal ∏ (M:precategory) (P Q : MorphismPair M^op) (f:MorphismPairIsomorphism P Q),
  opp_MorphismPairIsomorphism (opp_MorphismPairIsomorphism f) = f.
Proof.
  reflexivity.
Qed.
Goal ∏ (M:precategory) (P Q : MorphismPair M^op),
 MorphismPairIsomorphism (C:=M^op) P Q ->
 MorphismPairIsomorphism (C:=M) (MorphismPair_opp Q) (MorphismPair_opp P).
Proof.
  intros M P Q. exact (opp_MorphismPairIsomorphism (M:=M^op) ).
Qed.
Goal ∏ (M : AdditiveCategory), oppositeAdditiveCategory (oppositeAdditiveCategory M) = M.
Proof.
  reflexivity.
Defined.
Goal ∏ {M:AdditiveCategory} {X:Type} (j : X -> ob M) (su : sums_lift M j),
  opp_sums_lift (oppositeAdditiveCategory M) j (opp_sums_lift M j su) = su.
Proof.
  reflexivity.
Qed.
Goal ∏ (M:ExactCategoryData), oppositeExactCategoryData (oppositeExactCategoryData M) = M.
  reflexivity.
Qed.
Goal ∏ (M:ExactCategory), ExactCategoryDataToAdditiveCategory (ExactCategoryToData (oppositeExactCategory M))
                          = oppositeAdditiveCategory (ExactCategoryDataToAdditiveCategory (ExactCategoryToData M)).
Proof.
  reflexivity.
Defined.
Goal ∏ (M:ExactCategory), oppositeExactCategory (oppositeExactCategory M) = M.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:ExactCategory) (A B:M) (f : A --> B),
  isAdmissibleMonomorphism f = isAdmissibleEpimorphism (M:=oppositeExactCategory M) (opp_mor f).
Proof.
  reflexivity.
Defined.
Goal ∏ (M:ExactCategory) (A B:M) (f : A --> B), isAdmissibleEpimorphism f = isAdmissibleMonomorphism (M:=oppositeExactCategory M) (opp_mor f).
Proof.
  reflexivity.
Defined.
Goal ∏ (M:ExactCategory) (A B:M),
  AdmissibleMonomorphism A B = @AdmissibleEpimorphism (oppositeExactCategory M) B A.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:ExactCategory) (A B:M),
  AdmissibleEpimorphism A B = @AdmissibleMonomorphism (oppositeExactCategory M) B A.
Proof.
  reflexivity.
Defined.
Goal ∏ {M : ExactCategory} {A:M} (Z:Zero M), Mor1 (TrivialExactSequence A Z) = identity A.
  reflexivity.
Qed.
Goal ∏ {M : ExactCategory} {A:M} (Z:Zero M), Ob3 (TrivialExactSequence A Z) = Z.
  reflexivity.
Qed.
Goal ∏ {M : ExactCategory} {A:M} (Z:Zero M), Mor2 (TrivialExactSequence' Z A) = identity A.
  reflexivity.
Qed.
Goal ∏ {M : ExactCategory} {A:M} (Z:Zero M), Ob1 (TrivialExactSequence' Z A) = Z.
  reflexivity.
Qed.
Goal ∏ {M:ExactCategory} {X:Type} (j : X -> ob M) (ce : exts_lift M j),
  opp_exts_lift (M:=oppositeExactCategory M) j (opp_exts_lift (M:=M) j ce) = ce.
Proof.
  reflexivity.
Defined.

(** Exact category tests *)

Goal ∏ (M:precategory) (A A' B:M) (g : A --> B) (g' : A' --> B) (i:IsoArrowTo g g'),
  opposite_IsoArrowFrom (opposite_IsoArrowTo i) = i.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:precategory) (A B B':M) (g : A --> B) (g' : A --> B') (i:IsoArrowFrom g g'),
  opposite_IsoArrowTo (opposite_IsoArrowFrom i) = i.
Proof.
  reflexivity.
Defined.

Goal ∏ {M:precategory} {X:Type} (j : X -> ob M) (hz : zero_lifts M j),
  opp_zero_lifts (C:=opp_precat M) j (opp_zero_lifts (C:=M) j hz) = hz.
Proof.
  reflexivity.
Defined.

Goal ∏ (M:category), oppositeCategory (oppositeCategory M) = M.
  reflexivity.
Qed.

Goal ∏ {M:category} {a b c d : M} (f : b --> a) (g : c --> a)
     (p1 : d --> b) (p2 : d --> c),
  isPullback' f g p1 p2 = isPushout' (M := oppositeCategory M) f g p1 p2.
Proof.
  reflexivity.
Defined.

Goal ∏ {M:category} {a b c d : M} (f : a --> b) (g : a --> c)
     (in1 : b --> d) (in2 : c --> d),
  isPushout' f g in1 in2 = isPullback' (M := oppositeCategory M) f g in1 in2.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:precategory) (A A' B:M) (g : A --> B) (g' : A' --> B) (i:IsoArrowTo g g'),
  opposite_IsoArrowFrom (opposite_IsoArrowTo i) = i.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:precategory) (A B B':M) (g : A --> B) (g' : A --> B') (i:IsoArrowFrom g g'),
  opposite_IsoArrowTo (opposite_IsoArrowFrom i) = i.
Proof.
  reflexivity.
Defined.
Goal ∏ (M:PreAdditive) (x y z : M) (f : x --> y) (g : y --> z), isKernel' (M:=M) f g = isCokernel' (M:=oppositePreAdditive M) g f.
  reflexivity.
Defined.
Goal ∏ (M:PreAdditive) (x y z : M) (f : x --> y) (g : y --> z), isCokernel' (M:=M) f g = isKernel' (M:=oppositePreAdditive M) g f.
  reflexivity.
Defined.
Goal ∏ (M :PreAdditive) (A B C A':M) (i : A <-- B) (p : B <-- C)
      (pr : isKernelCokernelPair p i)
      (r : A <-- A') (pb : Pullback i r),
  PairPullbackMap pr r pb
  =
  PairPushoutMap (M:=oppositePreAdditive M) (opposite_isKernelCokernelPair pr) r pb.
Proof.
  reflexivity.
Defined.
Goal ∏ (M :PreAdditive) (A B C A':M) (i : A --> B) (p : B --> C)
      (pr : isKernelCokernelPair i p)
      (r : A --> A') (po : Pushout i r),
  PairPushoutMap pr r po
  =
  PairPullbackMap (M:=oppositePreAdditive M) (opposite_isKernelCokernelPair pr) r po.
Proof.
  reflexivity.
Defined.