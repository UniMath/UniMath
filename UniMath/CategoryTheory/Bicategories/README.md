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
* *Bicat.v* --- Definition of bicategory.
* *StandardBicategories.v* --- Various examples of bicategories.
* *OpCellBicat.v* ---Bicategory obtained by formally reversing 2-cells.
* *OpMorBicat.v* --- Bicategory obtained by formally reversing 1-arrows.
* *Unitors.v* --- Proof that let and right unitor coincide (incomplete).
* *PseudoFunctor.v* --- Definition of pseudofunctor.
* *Univalence.v* --- Univalence for bicategories.
* *BicatOfCats.v* --- bicategory of 1-category and pseudofunctor op.
* *Graph.v* --- Experiments with graphs (incomplete).

### Equivalence with with the presentation based on weakly enrighed 1-categories

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
