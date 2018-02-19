# (Co)inductive types

This directory contains some results about inductive and coinductive types.
Since UniMath doesn't support general definitions with Coq's (co)inductive
types, these types are instead studied in the form of W-types (resp. M-types),
which are characterized as initial (resp. final) algebras (resp. coalgebras) for
polynomial functors.

The proofs of uniqueness for M- and W-types are based on results in 
["Non-wellfounded trees in homotopy type theory"](https://arxiv.org/abs/1504.02949v1)
and [the corresponding Agda formalization](https://github.com/HoTT/m-types)
by Benedikt Ahrens, Paolo Capriotti, and Régis Spadotti.

The definition of fibered algebras is based on 
["Homotopy-initial algebras in type theory"](https://arxiv.org/abs/1504.05531v1)
and [the corresponding Coq formalization](https://github.com/kristinas/hinitiality)
by Benedikt Ahrens, Paolo Capriotti, and Régis Spadotti.

Package written by Langston Barrett (@siddharthist).
