Summary of various attempts to introduce resizing rules to get rid of -type-in-type

|     | RR1: $\frac{\Gamma\vdash is: isaprop X}{\Gamma\vdash X:Set}$  | $\frac{(U_j,U_K:Univ)(X:U_j) (k < j) (is: isaprop X)}{X:U_k}$   | $\frac{(U_j,U_K:Univ)(X:U_j) (k\le j) (is: isaprop X)}{X:U_k}$  | 
|-----|-----|---|---|
| RR2: $\frac{U:Univ}{\vdash (hProp U):Set}$ | proposed by Voevodsky    |   |   |
| RR2: $\frac{U:Univ}{\vdash (hProp U):U_1}, U_1$ above $Set$ |     |   | allowing for set quotients to be in $Set$    | 
| make_hprop 1 $\frac{(U_j, U_k, U_l:Univ)(j < k)(j < l)(X: U_k)(isaprop X)}{\vdash X:((hProp U_j):U_l)}$   |     |   |   |
| make_hprop 2 $\frac{(U_j, U_k, U_l:Univ)(k\le l)(j < l)(X: U_k)(isaprop X)}{\vdash X:((hProp U_j):U_l)}$   |     |   |  should allow for hprops of arbitrary sizes |   |


with definition of hprop as $hprop:= \sum_{X: U_k} isaprop(X): U_l$ for $k < l$ ($k\le l$ caused Coq to complain as it allows for `Type@{l} : Type@{l}`)

Another approach would be to add a resizing axiom instead of resizing rules, as for example done in the [HoTT Library](https://github.com/HoTT/Coq-HoTT/blob/master/theories/PropResizing/PropResizing.v). 