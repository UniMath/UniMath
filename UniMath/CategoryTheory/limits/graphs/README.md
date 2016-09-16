graphs
============

This directory contains a development of limits on the basis of
descriptions of diagrams by graphs instead of functors.

It is often better to use the direct implementation of specific limits
in the parent folder for efficiency reasons. For instance we have
noticed that changing the proof that binary (co)products lift to
functor categories to the general one for limits makes the compilation
of SubstitutionSystems very slow.

## Contents

* *colimits.v*
  * definition of graph and diagram
  * formalization of colimits on this basis
  * rules for pre- and post-composition
  * pointwise construction of colimits in functor precategories
* *limits.v*
  * formalization of limits on the basis of graphs
  * proof that limits form a property in a (saturated/univalent) category
  * pointwise construction of limits in functor precategories
  * alternative definition of limits via colimits
* *initial.v* --- definition as instance of colimit
* *terminal.v* --- definition as instance of limit
* *binproducts.v* --- formalization as instance of limit
* *bincoproducts.v* --- formalization as instance of colimit
* *pullbacks.v* --- formalization as instance of limit
* *pushouts.v* --- formalization as instance of colimit
* *equalizers.v* --- formalization as instance of limit
* *coequalizers.v* --- formalization as instance of colimit
* *kernels.v* --- formalization as instance of limit
* *cokernels.v* --- formalization as instance of colimit
* *zero.v* --- formalization within the approach of this directory
