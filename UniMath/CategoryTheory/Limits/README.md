limits
===============

This directory contains the definition of some limits for the notion
of precategory defined in the package *CategoryTheory* which formerly
had the name "RezkCompletion".

## Contents

* *cones.v*
  * definition of the precategory of cones over precategory C
  * proof that that precategory is a category if C is
* *initial.v*
  * direct formalization of initial objects
  * proof that initial object is a property in a category
  * link with empty coproduct
  * initial element in functor precategory
* *terminal.v*
  * direct formalization of terminal objects
  * proof that terminal object is a property in a category
  * link with empty product
* *Pullbacks.v*
  * direct formalization of pullbacks
  * proof that pullbacks form a property in a (saturated/univalent) category
  * symmetry
  * on sections
  * pullback chasing
  * reflection and preservation
  * pointwise constructions in functor precategory
  * construction of products from pullbacks
* *binproducts.v*
  * direct formalization of binary product
  * definition of binary product functor
* *bincoproducts.v*
  * direct formalization of binary coproduct
  * proof that binary coproduct(cocone) is a property in a category
  * specialized versions of beta rules for coproducts
  * definition of binary coproduct functor
* *products.v* --- direct generalization to arbitrary products
* *coproducts.v* --- direct generalization to arbitrary coproducts
* *Equalizers.v*
  * direct formalization of equalizer
  * equalizer arrows are monic
* *Coequalizers.v*
  * direct formalization of coequalizer
  * coequalizer arrows are epi
* *zero.v* --- direct formalization of zero objects
* *Kernels.v* --- direct formalization of kernels
* *Cokernels.v* --- direct formalization of cokernels
* *FunctorsPointwiseBinProduct.v*  --- definition of a binary product structure on a functor category by taking pointwise binary products in the target category
* *FunctorsPointwiseBinCoproduct.v* --- definition of a coproduct structure on a functor category by taking pointwise binary coproducts in the target category; option functor as special case
* *FunctorsPointwiseProduct.v* --- same with arbitrary products
* *FunctorsPointwiseCoproduct.v* --- same with arbitrary coproducts
* *Graphs* --- development of limits on the basis of descriptions of diagrams by graphs
* *Cats* --- development of limits on the basis of descriptions of diagrams by functors

