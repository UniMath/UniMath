(*******************************************************************************************

 The tripos to topos construction

 In this file, we show that every tripos gives rise to a topos.

 Recall that a tripos is given by a first-order hyperdoctrine in which one can take powersets.
 Intuitively, a tripos is a categorical structure in which one can interpret impredicative
 higher-order intuitionistic logic. The first-order hyperdoctrine gives us a setting for
 intuitionistic predicate logic, and by assuming that we can take powersets, we obtain
 impredicativity. Every tripos gives rise to a generic object, which is the object of all
 propositions in the hyperdoctrine. The generic object is defined to be the powerset of the
 terminal object (compare to the fact that hProp is equivalent to the powerset of the unit type).
 A precise definition of triposes can be found in "Tripos Theory in Retrospect" by Andrew Pitts
 and in the file `Tripos.v`.

 Every tripos gives rise to the following category.
 - The objects of this category are partial setoids. These are given by an object in [C]
   together with a partial equivalence relation (i.e., symmetric and transitive relation).
   We denote these by [(X , ~)], and they are defined in the file `PartialEqRels.PERs.v`.
 - The morphisms from [(X , ~)] to [(Y , ~)] are given by functional relations between [X]
   and [Y]. We define these in the file `PartialEqRels.PERMorphisms.v` and we prove that this
   data forms a category in `PartialEqRels.PERCategory.v`.
 - To prove that this category has finite limits, we construct binary products, equalizers, and a
   terminal object. The terminal object and binary products are constructed using the structure
   of [C]. Here we use that the category [C] has a terminal object and binary products by
   definition of first-order hyperdoctrines. To construct equalizers, we use the fact that
   the equivalence relations are partial. We define these in the follows files:
   + `PartialEqRels.PERBinProducts.v`
   + `PartialEqRels.PEREqualizers.v`
   + `PartialEqRels.PERTerminal.v`
 - We construct exponentials by using that functions can be represented as relations that
   satisfy certain properties (i.e., functions are relations of pairs). This is possible since
   in a tripos, we can take powersets. The construction is split over several files, and the
   relevant identifier is given in `PartialEqRels.PERExponentials.v`.
 - The subobject classifier is constructed as the generic predicate (i.e., the powerset of the
   terminal object) and we identify elements of the generic predicate if they are logically
   equivalent. The construction is in `PartialEqRels.PERSubobjectClassifier.v`.
 This shows that the category of partial setoids is a topos, and thus every tripos gives rise
 to a topos.

 Note that the tripos-to-topos construction satisfies a universal property. We have a
 pseudofunctor from toposes to first-order hyperdoctrines, which sends every topos to the
 first-order hyperdoctrine of subobjects. The tripos-to-topos construction gives a left
 biadjoint to this pseudofunctor, see Theorem 3.6 in "Tripos Theory in Retrospect".

 There are several important instances of the tripos to topos construction, and these are
 described in "Tripos Theory in Retrospect" by Andrew Pitts. First, the category of [H]-valued
 sets can be constructed using the tripos to topos construction (here [H] is a Heyting algebra).
 This construction is used in the context of forcing and independence proofs. Second,
 realizability toposes can be constructed using the tripos to topos construction, see for
 instance "Realizability: an introduction to its categorical side" by Jaap van Oosten. Note
 that the tripos to topos construction does not necessarily give rise to a univalent category,
 and thus one needs to take its Rezk completion in order to get a univalent topos.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Realizability: an introduction to its categorical side" by Jaap van Oosten

 *******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.PowerObject.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PEREqualizers.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERSubobjectClassifier.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialEval.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialLam.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialEqs.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERExponentials.

Definition tripos_to_topos
           (H : tripos)
  : Topos.
Proof.
  use make_Topos.
  - exact (category_of_partial_setoids H).
  - use make_Topos_Structure.
    + use Pullbacks_from_Equalizers_BinProducts.
      * exact (binproducts_partial_setoid H).
      * exact (equalizers_partial_setoid H).
    + exact (terminal_partial_setoid H).
    + exact (subobject_classifier_partial_setoid H).
    + use PowerObject_from_exponentials.
      exact (exponentials_independent _ _ (exponentials_partial_setoid H)).
Defined.
