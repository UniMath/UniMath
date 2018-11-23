Bicategories
============

Bicategories, displayed bicategories and some applications, including
Categories with Families (CwF).

Contributed by Benedikt Ahrens, Marco Maggesi, February 2018.

Directory WkCatEnrichment contains an alternative definition of
bicategory in the style of enrichment in 1-categories contributed by
Mitchell Riley (see https://github.com/UniMath/UniMath/pull/409).

## Contents

### Basics about bicategories
* *Bicat.v*
  * Definition of (pre)bicategories and builder functions
  * Invertible 2cells and some lemmas about them
  * Derived equations in bicategories (e.g., interchange law)
  * To weakly enriched definition of bicategories
  * Discrete and chaotic bicategories
* *BicatAliases.v*
* *bicategory_laws.v*
  * Derived equations in bicategories, imported from Dan Frumin and Niels van der Weide's library
* *bicategory_laws_2.v*
  * Derived equations about invertible 2cells, imported from Dan Frumin and Niels van der Weide's library
* *composition.v*
  * Composition of lax functors and pseudo functors
* *equiv_to_adjequiv.v*
  * Adjointification theorem for bicategories
* *identity.v*
  * Identity pseudo functor
* *transport_laws.v*
  * Transport of 2cells along equalities of 0cells and 1cells
* *ap_functor.v*
  * A function of types induces a pseudo functor between their fundamental bigroupoids
* *StandardBicategories.v* --- Various examples of bicategories.
* *OpCellBicat.v* ---Bicategory obtained by formally reversing 2-cells.
* *OpMorBicat.v* --- Bicategory obtained by formally reversing 1-arrows.
* *Unitors.v* 
  * Proof that let and right unitor coincide
* *PseudoFunctor.v* 
  * Definition of lax functor
  * Pseudo functors as subtype of lax functors
* *Univalence.v*
  * Internal adjunction
  * Internal equivalence
  * Composition of internal equivalences is an internal equivalence
  * Formulation of local and global univalence
* *adjoint_unique.v*
  * In locally univalent bicats, being an adjoint equivalence is a proposition
  * Corollary: such adjoint equivalences are equal if their underlying 1cells are
* *BicatOfCats.v* --- bicategory of 1-category and pseudofunctor op.
* *Graph.v* --- Experiments with graphs (incomplete).

### Equivalence with with the presentation based on weakly enriched 1-categories

* *WkCatEnrichment* --- Subdirectory with the definition of bicategory as enriched in 1-categories.
* *BicategoryOfBicat.v* --- Translation to bicategories as defined in WkCatEnrichment.
* *BicatOfBicategory.v* --- Translation from bicategories as defined in WkCatEnrichment.

### Displayed bicategories and other constructions

* *DispBicat.v* --- Definition of displayed bicategory.
* *DispBicatOfDispCats.v* --- Displayed bicategory of displayed structures on 1-categories.
* *DispUnivalence.v* --- Internal adjunction in displayed bicategories.
* *ContravariantFunctor.v* --- Displayed bicategory of contravariant functors into a fixed category K.
* *Constructions.v* --- Basic constructions of displayed and non displayed bicategories (displayed direct product, full subcategory, ...).
* *Sigma.v* ---
* *Fibration.v* ---
* *Cofunctormap.v* ---

### Application: Categories with Families (CwF)

* *CwF.v* --- Definition of category with families.
