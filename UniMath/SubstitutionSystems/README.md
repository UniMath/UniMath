# Heterogeneous substitution systems

Formalization of heterogeneous substitution systems as defined in

Matthes & Uustalu, [Substitution in Non-wellfounded Syntax with Variable Binding](http://www.irit.fr/~Ralph.Matthes/papers/MatthesUustalu-final.pdf)


Report on the formalization and some additional results are given in

Ahrens & Matthes, [Heterogeneous substitution systems revisited](http://arxiv.org/abs/1601.04299)

Much more on signatures (binding signatures and signatures with strength) and effective constructions of initial algebras and fortiori heterogeneous substitution systems and monads is described in

Ahrens, Matthes & Mörtberg, [From signatures to monads in UniMath](https://arxiv.org/abs/1612.00693)

Still more recent material by Ahrens, Matthes & Mörtberg concerns multi-sorted systems.


* *MultiSorted.v* --- the main file on multi-sorted binding signatures
* *MonadsMultiSorted.v* --- an exploration of what a monad allows to do in the slice category
* *STLC.v* --- the example of simply-typed lambda calculus
* *CCS.v* --- the example of the calculus of constructions in the style of Streicher
Not surprisingly, these files heavily depend on the implementation of category theory that had to be extended to fit the needs.


# Contents (alphabetic order of files)

* *BindingSigToMonad.v*
  * defines the notion of binding signature which captures a decidable set of constructors with finitely many binders in their finitely many arguments - this is a purely syntactic definition
  * signatures with strength are derived
  * get an initial algebra interpreting the binding signature and get the associated initial heterogeneous substitution system and monad
* *BinProductOfSignatures.v* --- in particular infers strength for the binary product and proves omega-cocontinuity 
* *BinSumOfSignatures.v* --- same with binary sums instead of binary products (needed to model finitely many constructors)
* *FromBindingSigsToMonads_Summary.v* --- provides a stable interface to
  the formalization described in the paper by Ahrens, Matthes & Mörtberg (with the correspondence to the numbering of the
  definitions, lemmas and theorems)
* *GenMendlerIteration.v*
  * assumes an initial algebra
  * Derivation of Generalized Mendler Iteration
  * Instantiation to a special case, Specialized Mendler Iteration
  * Proof of a fusion law à la Bird-Paterson (Generalised folds for nested datatypes) for Generalized Mendler Iteration
* *GenMendlerIteration_alt.v* --- a variant of GenMendlerIteration.v that differs in the hypotheses: here we use
  ω-cocontinuity instead of Kan extensions (also based on the paper by Bird & Paterson)
* *LamFromBindingSig.v*
  * signature of lambda calculus obtained from general constructions
  * equational laws for catamorphisms/folds on lambda calculus
  * obtain substitution monad on Set
* *LamHSET.v* --- instantiates the main result of LiftingInitialAlt.v for Lam in the category HSET and obtains an
  initial heterogeneous substitution system and a monad
* *LamSignature.v*
  * "Manual" definition of the arities of the constructors of lambda calculus
  * "Manual" definition of the signatures of lambda calculus and lambda calculus with explicit flattening
  * ω-cocontinuity only for lambda calculus established by reference to general results, no such result for lambda
    calculus with explicit flattening
* *Lam.v*
  * Specification of an initial morphism of substitution systems from lambda calculus with explicit flattening to
    lambda calculus
  * the bracket property still has a very long monolithic proof
* *LiftingInitial.v*
  * Construction of a substitution system from an initial algebra 
  * Proof that the substitution system constructed from an initial algebra is an initial substitution system
* *LiftingInitialAlt.v* --- a variant of LiftingInitial.v that differs in the hypotheses: here we use ω-cocontinuity
  instead of Kan extensions (this means we use GenMendlerIteration_alt.v instead of GenMendlerIteration.v
* *MLTT79.v* --- the syntax of Martin-Löf's type theory in the style of LamHSET.v
* *MonadsFromSubstitutionSystems.v*
  * Construction of a monad from a substitution system
  * Proof that morphism of hss gives morphism of monads
  * Bundling that into a functor
  * Proof that the functor is faithful
* *Notation.v* --- notation that is used in this package but that is not specific to the topic of the package
* *SignatureCategory.v*
  * organize signatures with strength into a category as described in the paper by Ahrens, Matthes & Mörtberg
  * identify coproducts and binary products
* *SignatureExamples.v*
   * provides a general construction of θ in a signature in the case when the functor is precomposition with a
     functor G by starting with a family of simpler distributive laws δ
   * multiplication of distributive laws δ
   * distributive laws δ for option and iterations of a functor
* *Signatures.v*
  * Definition of signatures with strength
  * Proof that two forms of strength laws are equivalent
* *SubstitutionSystems_Summary.v* --- provides a stable interface to
  the formalization of heterogeneous substitution systems as described in the paper by Ahrens & Matthes
* *SubstitutionSystems.v*
  * Definition of heterogeneous substitution systems
  * Various lemmas about the substitution ("bracket") operation
  * Definition of precategory of substitution systems
* *SumOfSignatures.v* --- generalization of BinSumOfSignatures.v to sums over a decidable index set





