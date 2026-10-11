Monads within CategoryTheory
============================

A wild mix of material from multiple authors.

## Contents

* *Monads.v* --- monads based on monad multiplication, def. of bind operation and substitution, a rawer data format for such monads, monad construction from adjunction
* *KleisliCategory.v* --- Kleisli category based on def. in Monads.v and its canonical adjunction
* *RelativeMonads.v* --- relative monads (naturally in the setting of Kleisli triples), their Kleisli category (and its canonical relative adjunction), univalence
* *KTriples.v* --- monads based on Kleisli triples (i.e., with Haskell-style bind operator), which are a special case of the relative monads
* *KTriplesEquiv.v* --- establishes an isomorphism of categories between monads based on monad multiplication and on bind (Kleisli triples)
* *Kleisli.v* --- weak equivalence between the "Kleisli" definition of monads (instantiated from RelativeMonads.v) and the "monoidal" definition (with monad multiplication)
* *LModules.v* --- left modules over a monad, with pullback constructions
* *Derivative.v* --- "maybe" monad, distributive laws for pairs of monads, composition of monads, derivative of a monad and a left module of a monad
* *RelativeModules.v* --- modules over relative monads (generalizing material from LModules.v)
* *MonadAlgebras.v* --- category of algebras of a monad, free-forgetful adjunction between algebras and base category
