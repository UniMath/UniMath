# Logical equivalence

There are (at least) three notions of "equivalence" at play in UniMath.

 1. The strongest (and perhaps most important) is _weak equivalence_ (`weq`),
    denoted `≃`.
 2. _Logical equivalence_ (`logeq`) is denoted `<->`. Two types
    `A` and `B` are logically equivalent if there are functions `A -> B` and 
    `B -> A`.
 3. _Bi-implication_ or _h-equivalence_ is just logical equivalence
    specialized to `hProp`s.
    
This package provides elementary lemmas about the second and third ones.
Sometimes, weak equivalences can be turned into logical equivalences, and so
on into bi-implication, and this is done where possible.
