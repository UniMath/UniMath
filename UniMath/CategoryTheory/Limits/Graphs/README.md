Graphs
============

This directory contains a development of limits on the basis of
descriptions of diagrams by graphs instead of functors.

It is often better to use the direct implementation of specific limits
in the parent folder for efficiency reasons. For instance we have
noticed that changing the proof that binary (co)products lift to
functor categories to the general one for limits makes the compilation
of SubstitutionSystems very slow.

## Contents

* *Colimits.v*
  * definition of graph and diagram
  * formalization of colimits on this basis
  * rules for pre- and post-composition
  * pointwise construction of colimits in functor precategories
* *Limits.v*
  * formalization of limits on the basis of graphs
  * proof that limits form a property in a (saturated/univalent) category
  * pointwise construction of limits in functor precategories
  * alternative definition of limits via colimits
* *Initial.v* --- definition as instance of colimit
* *Terminal.v* --- definition as instance of limit
* *Binproducts.v* --- formalization as instance of limit
* *Bincoproducts.v* --- formalization as instance of colimit
* *Pullbacks.v* --- formalization as instance of limit
* *Pushouts.v* --- formalization as instance of colimit
* *Equalizers.v* --- formalization as instance of limit
* *Coequalizers.v* --- formalization as instance of colimit
* *Kernels.v* --- formalization as instance of limit
* *Cokernels.v* --- formalization as instance of colimit
* *Zero.v* --- formalization within the approach of this directory
