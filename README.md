Rezk Completion
===============

This Coq library mechanizes the Rezk completion as described in
http://arxiv.org/abs/1303.0584

It builds upon V. Voevodsky's Foundations library, available on
http://arxiv.org/abs/1401.0053

## Requirements

### Coq

The library compiles under Coq8.3pl5, patched according to the instructions given in 
http://arxiv.org/abs/1401.0053. 
Lower patch levels of Coq8.3, e.g., Coq8.3pl2, are likely to work as well.

### Libraries

Files used from V. Voevodsky's Foundations:

  - uuu.v
  - uu0.v
  - hProp.v
  - hSet.v
  - funextfun.v

They should be installed in the user-contrib/Foundations directory of Coq, so
Coq can find them. 

