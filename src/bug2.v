Require Import Foundations.hlevel2.algebra1a.
Parameter X : hSet.
Parameter n : X -> X -> X.
Parameter n': X -> X -> X.
Definition S := setwithbinoppair X n.
Definition S':= setwithbinoppair X n'.
Definition weird (s:S) (s':S') := op s s'.
