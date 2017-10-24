Category Theory
===============

This evolved from the package "Rezk Completion" whose authors are: Benedikt Ahrens, Chris Kapulkin, Mike Shulman

Hence, this Coq library in particular mechanizes the Rezk completion as described in
http://arxiv.org/abs/1303.0584.
It was written by Benedikt Ahrens, Chris Kapulkin and Mike Shulman.

It builds upon V. Voevodsky's Foundations library, available on
http://arxiv.org/abs/1401.0053.

For any question about this library, send an email to Benedikt Ahrens.

## Contents

### The files containing the formalization of the Rezk Completion:

* *precategories.v*
  * precategories
  * isomorphisms in precategories
* *functor_categories.v*
  * functors and natural transformations
  * various properties of functors
  * the functor precategory is a category if the target category is
* *sub_precategories.v*
  * sub-precategories
  * image factorization of a functor
  * a full subprecategory of a category is a category
* *equivalences.v*
  * definition of adjunction
  * adjoint equivalence of precategories
  * proof that an adjoint equivalence of categories yields a weak equivalence of objects
  * a fully faithful and essentially surjective functor induces equivalence of precategories if its source is a category
* *HLevel_n_is_of_hlevel_Sn.v* --- the type of types of hlevel n is itself of hlevel n+1
* *category_hset.v*
  * definition of the precategory of sets
  * proof that it is a category
* *yoneda.v*
  * definition of Yoneda embedding
  * proof that it is fully faithful
* *whiskering.v*
  * definition of whiskering
* *precomp_fully_faithful.v*
  * precomposition with a fully faithful and essentially surjective functor yields a fully faithful functor
* *precomp_ess_surj.v*
  * precomposition with a fully faithful and essentially surjective functor yields an essentially surjective functor
* *rezk_completion.v*
  * put the previous files together and exhibit the Rezk completion

### many more files that were not needed for the Rezk completion and that go beyond the former package "Rezk Completion"; they have various authors (see the files individually that are given in alphabetic order):
* *AbelianToAdditive.v* --- AbelianPreCat is Additive
* *Abelian.v* --- abelian categories
* *AdditiveFunctors.v*
* *Additive.v* --- additive categories
* *AdjunctionHomTypesWeq.v*
  * Derivation of the data of an adjunction in terms of equivalence of hom-types from the definition of adjunction in terms of unit and counit
* *category_abgr.v* --- category of abelian groups
* *category_binops.v* --- category of sets with binary operations
* *category_hset_structures.v* --- limits, colimits and exponentials in HSET
* *catiso.v* --- isomorphism of (pre)categories
* *CocontFunctors.v* --- theory about (omega-)cocontinuous functors
* *CohomologyComplex.v* --- cohomology of complexes
* *CommaCategories.v* --- special comma categories (c ↓ K)
* *Complexes.v*c --- category of complexes over an additive category
* *covyoneda.v* --- covariant Yoneda functor
* *DiscretePrecategory.v*
* *EndofunctorsMonoidal.v*
  * Definition of the (weak) monoidal structure on endofunctors
* *Epis.v*
* *EquivalencesExamples.v* --- some adjunctions
  * binary delta_functor is left adjoint to binproduct_functor
  * general delta functor is left adjoint to the general product
  functor
  * bincoproduct_functor is left adjoint to the binary delta functor
  * general coproduct functor is left adjoint to the general delta
  functor
  * swapping of arguments in functor categories
* *equivalences_lemmas.v*
  * definition of adjunction
  * definition of equivalence of precategories
  * some results
* *exponentials.v*
* *FunctorAlgebras.v* --- algebras of an endofunctor, Lambek's lemma
* *GrothendieckTopos.v*
* *HorizontalComposition.v*
  * Definition of horizontal composition for natural transformations
* *Kleisli.v* --- the "Kleisli" definition of monad and its equivalence to the "monoidal" definition
* *LocalizingClass.v* --- localizing class and localization of categories
* *Monads.v* --- monads, bind operation and substitution
* *Monics.v* --- monics, their subcategory and their construction in functor categories
* *Morphisms.v*
  *pair of morphisms*
  *short exact sequence data*
* *opp_precat.v* --- opposite pre-category
* *PointedFunctors.v*
  * Definition of precategory of pointed endofunctors
  * Forgetful functor to precategory of endofunctors
* *PointedFunctorsComposition.v*
  * Definition of composition of pointed functors
* *PreAdditive.v* --- preadditive categories
* *PrecategoriesWithAbgrops.v* --- precategories whose homsets are abelian groups
* *precategoriesWithBinOps.v* --- precategories such that spaces of morphisms have a binary operation
* *PrecategoryBinProduct.v*
  * Definition of the cartesian product of two precategories
  * From a functor on a product of precategories to a functor on one of the categories by fixing the argument in the other component
* *ProductPrecategory.v* --- general product category, not just binary product
* *Quotobjects.v* --- quotient objects
* *RightKanExtension.v*
  * Definition of global right Kan extension as right adjoint to precomposition
* *RModules.v* --- right modules over a monad
* *ShortExactSequences.v*
* *slicecat.v* --- slice precategories and colimits therein
* *Subobjects.v*
* *total2_paths.v* --- paths in total spaces are equivalent to pairs of paths (for fibrations over the universe)
* *UnderPrecategories.v*
* *UnicodeNotations.v* --- very few notations: -->, ;;, #F, C ⟦ a , b ⟧
  
### The subdirectories

* *limits*
  * definition of some limits and colimits
  * proof that they are unique in categories
  * with subdirectories cats and graphs
* *bicategories* by Mitchell Riley
  * with 6 .v files there: notations.v, bicategory.v, Cat.v, internal_equivalence.v, prebicategory.v, whiskering.v
* *Inductives* by Anders Mörtberg
  * with three case studies: Lists.v, Trees.v, LambdaCalculus.v
