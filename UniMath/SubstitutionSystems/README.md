# Heterogeneous substitution systems

Formalization of heterogeneous substitution systems as defined in

Matthes & Uustalu, [Substitution in Non-wellfounded Syntax with Variable Binding](http://www.irit.fr/~Ralph.Matthes/papers/MatthesUustalu-final.pdf)

# Contents

* *AdjunctionHomTypesWeq.v*
  * Derivation of the data of an adjunction in terms of equivalence of hom-types from the definition of adjunction in terms of unit and counit
* *Auxiliary.v*
  * various helper lemmas that should be moved upstream
* *EndofunctorsMonoidal.v*
  * Definition of the (weak) monoidal structure on endofunctors
* *FunctorsPointwiseCoproduct.v*
  * Definition of a coproduct structure on a functor category by taking pointwise coproducts in the target category
* *FunctorsPointwiseProduct.v*
  * Definition of a product structure on a functor category by taking pointwise products in the target category
* *GenMendlerIteration.v*
  * Derivation of Generalized Mendler Iteration
  * Instantiation to a special case, Specialized Mendler Iteration
  * Proof of a fusion law à la Bird-Paterson (Generalised folds for nested datatypes) for Generalized Mendler Iteration
* *HorizontalComposition.v*
  * Definition of horizontal composition for natural transformations
* *LamSignature.v*
  * Definition of the arities of the constructors of lambda calculus
  * Definition of the signatures of lambda calculus and lambda calculus with explicit flattening
* *Lam.v*
  * Specification of an initial morphism of substitution systems from lambda calculus with explicit flattening to lambda calculus
* *LiftingInitial.v*
  * Construction of a substitution system from an initial algebra 
  * Proof that the substitution system constructed from an initial algebra is an initial substitution system
* *MonadsFromSubstitutionSystems.v*
  * Construction of a monad from a substitution system
  * Proof that morphism of hss gives morphism of monads
  * Bundling that into a functor
  * Proof that the functor is faithful
* *PointedFunctors.v*
  * Definition of precategory of pointed endofunctors
  * Forgetful functor to precategory of endofunctors
* *PointedFunctorsComposition.v*
  * Definition of composition of pointed functors
* *ProductPrecategory.v*
  * Definition of the cartesian product of two precategories
  * From a functor on a product of precategories to a functor on one of the categories by fixing the argument in the other component
* *RightKanExtension.v*
  * Definition of global right Kan extension as right adjoint to precomposition
* *Signatures.v*
  * Definition of signatures
  * Proof that two forms of strength laws are equivalent
* *SubstitutionSystems.v*
  * Definition of heterogeneous substitution systems
  * Various lemmas about the substitution ("bracket") operation
  * Definition of precategory of substitution systems
* *SumOfSignatures.v*
  * Definition of the sum of two signatures, in particular proof of strength laws for the sum





