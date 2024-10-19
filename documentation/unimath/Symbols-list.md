UniMath uses both ASCII and Unicode notation. Below we give an overview of the most important symbols.
To see how to input a specific Unicode character, type
`C-u C-x =` (meaning: hold CTRL, then press u and x; release CTRL, press =) while hovering over that character.

Below is a partial list of Unicode symbols and identifiers used in UniMath.

| Item                       | UniMath symbol  | Unicode input                  |UniMath ASCII alternative |
| -------------------------- | --------------- | ------------------------------ | ------------------------ |
|   **Type and term constructors**
| Product type               |  `∏ (x : A), B` | `\prod`                        | `forall x : A, B`        |
| Function type              | `A → B`         | `\to`                          | `A -> B`                 |
| Lambda abstraction         |  `λ x, e`       | `\lambda`                      | `fun x => e`             |
| Sigma type                 | `∑ (x : A), B`  | `\sum`                         | `total2 (fun x => B)`    |
| Cartesian product type     |  `X × Y`        | `\times`                       | `dirprod X Y`            |
| Pair term                  |  `a,,b`         |                                | `a,,b`                   |
| Coproduct type             | `X ⨿ Y`         | `\union` then select from menu | `coprod X Y`             |
| Identity type              | `a = b`         |                                | `a = b`                  |
|   **Univalent logic in `hProp`**
| Conjunction                | `A ∧ B`         | `\and`                         | `hconj A B`              |
| Disjunction                | `A ∨ B`         | `\or`                          | `hdisj A B`              |
| Implication                | `A ⇒ B`         | `\=>`                          | `himpl A B`              |
| Negation                   | `¬ X`           | `\neg`                         | `hneg X`                 |
| Universal quantification   | `∀  x , P x`    | `\forall`                      | `forall_hProp A`         |
| Existential quantification | `∃ x, P x`      | `\ex`                          | `hexists P`              |
| Propositional truncation   | `∥ A ∥`          | `\\|\|`                        | `ishinh A`               |
|   **Category theory**
| Object type of `C`         | `ob C` or `C`   |                                |                          |
| Morphisms                  | `C⟦a,b⟧`        | `\[[` and `\]]`                |  `a --> b`               |
| Functor `F` on objects     | `F a`           |                                |                          |
| Functor `F` on morphisms   | `#F f`          |                                |                          |
