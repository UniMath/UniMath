Rezk Completion
===============

This Coq library mechanizes the Rezk completion as described in
http://arxiv.org/abs/1303.0584.
It was written by Benedikt Ahrens, Chris Kapulkin and Mike Shulman.

It builds upon V. Voevodsky's Foundations library, available on
http://arxiv.org/abs/1401.0053.

For any question about this library, send an email to Benedikt Ahrens.

## Contents

### The toplevel files

The toplevel files contain the formalization of the Rezk Completion:

* *precategories.v* --- precategories and isomorphisms therein
* *functors_transformations.v* --- functors and natural transformations; various properties of functors; the functor precategory is a category if the target category is
* *sub_precategories.v* --- sub-precategories and the image factorization of a functor; full subprecategory of a category is a category
* *equivalences.v* --- definition of adjunction, adjoint equivalence of precategories; proof that ad. equiv. of categories yields weak equivalence of objects;
                         a fully faithful and essentially surjective functor induces equivalence of precategories if source is a category
* *category_hset.v* --- definition of the precategory of sets and proof that it is a category
* *yoneda.v* --- definition of Yoneda embedding and proof that it is fully faithful
* *whiskering.v* --- definition of whiskering
* *precomp_fully_faithful.v* --- Precomposition with a fully faithful and essentially surjective functor yields a fully faithful functor
* *precomp_ess_surj.v* --- Precomposition with a fully faithful and essentially surjective functor yields an essentially surjective functor
* *rezk_completion.v* --- that puts the previous files together exhibiting the Rezk completion

### The subdirectories

* *limits* --- definition of some limits and proof that they are unique in categories


## Requirements

This package depends on the package *Foundations* which is also part of this repository. 
There is hence no need to install extra stuff to use this package; we only list the precise dependencies
for the sake of completeness.

### Libraries

Files used from V. Voevodsky's Foundations, available from the package *Foundations*:

  - uuu.v
  - uu0.v
  - hProp.v
  - hSet.v
  - funextfun.v



