# Heterogeneous substitution systems

Formalization of heterogeneous substitution systems as defined in

Matthes & Uustalu, [Substitution in Non-wellfounded Syntax with Variable Binding](http://www.irit.fr/~Ralph.Matthes/papers/MatthesUustalu-final.pdf)


Report on the formalization and some additional results are given in

Ahrens & Matthes, [Heterogeneous substitution systems revisited](http://arxiv.org/abs/1601.04299)

# Contents (alphabetic order of files)

* *BinProductOfSignatures.v* --- in particular infers strength for the product and proves omega-cocontinuity 
* *BinSumOfSignatures.v* --- same with sums instead of products (needed to model finitely many constructors)
* *GenMendlerIteration.v*
  * assumes an initial algebra
  * Derivation of Generalized Mendler Iteration
  * Instantiation to a special case, Specialized Mendler Iteration
  * Proof of a fusion law à la Bird-Paterson (Generalised folds for nested datatypes) for Generalized Mendler Iteration
* *GenSigToMonad.v*
  * defines the notion of "general signature" which captures a decidable set of constructors with finitely many binders in their finitely many arguments - this is a purely syntactic definition
  * signatures in the sense of this package are derived
  * a lot of material also from CategoryTheory is employed to get an initial algebra interpreting the general signature and getting the associated initial heterogeneous substitution system and monad
* *LamFromGenSig.v*
  * signature of lambda calculus obtained from general constructions starting from a "general signatures" (a variation on the development in LamFromSig.v)
* *LamFromSig.v*
  * signature of lambda calculus obtained from general constructions
  * equational laws for catamorphisms/folds on lamba calculus
* *LamHSET.v* --- instantiates the main result of LiftingInitial.v for Lam in the category HSET and obtains an initial heterogeneous substitution system and a monad
* *LamSignature.v*
  * "Manual" definition of the arities of the constructors of lambda calculus
  * "Manual" definition of the signatures of lambda calculus and lambda calculus with explicit flattening
  * omega-cocontinuity only for lambda calculus established by reference to general results, no such result for lambda calculus with explicit flattening
* *Lam.v*
  * Specification of an initial morphism of substitution systems from lambda calculus with explicit flattening to lambda calculus
  * the bracket property still has a very long monolithic proof
* *LiftingInitial.v*
  * Construction of a substitution system from an initial algebra 
  * Proof that the substitution system constructed from an initial algebra is an initial substitution system
* *MLTT79.v* --- the syntax of Martin-Löf's type theory in the style of LamFromGenSig.v
* *MonadsFromSubstitutionSystems.v*
  * Construction of a monad from a substitution system
  * Proof that morphism of hss gives morphism of monads
  * Bundling that into a functor
  * Proof that the functor is faithful
* *Notation.v* --- notation that is used in this package but that is not specific to the topic of the package
* *SignatureExamples.v*
   * provides a general construction of θ in a signature in the case when the functor is precomposition with a functor G by starting with a family of simpler
   distributive laws δ
   * multiplication of distributive laws δ
   * distributive laws δ for option and iterations of a functor
* *Signatures.v*
  * Definition of signatures
  * Proof that two forms of strength laws are equivalent
* *SigToMonad.v*
  * based on syntactic notion of signature that underlies LamFromSig.v
  * puts together all the needed semantic signature lemmas over HSET as base category, instantiates main results for obtaining a monad 
* *SubstitutionSystems_Summary.v* --- provides a stable interface to
  the formalization of heterogeneous substitution systems as
  defined by Matthes and Uustalu
* *SubstitutionSystems.v*
  * Definition of heterogeneous substitution systems
  * Various lemmas about the substitution ("bracket") operation
  * Definition of precategory of substitution systems
* *SumOfSignatures.v* --- generalization of BinSumOfSignatures.v to sums over a decidable index set





