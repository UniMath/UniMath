# The bicategory of display map categories

## Direct vs. displayed version

`BicatOfDisplayMapCat.v` contains a direct construction with a terminal object in the base category.
Everything in that file is mirrored in the displayed version in `DispBicatOfDisplayMapCat.v`.
Therefore, the displayed version should be used, as it also contains extra definitions and theorems.

|                                                                    | `BicatOfDisplayMapCat.v` | `DispBicatOfDisplayMapCat.v`                                 |
|:-------------------------------------------------------------------|:------------------------:|:------------------------------------------------------------:|
| bicategory of display map categories                               |                          | displayed over `bicat_of_univ_cats`                          |
| univalence of bicategory of DMCs                                   |                          | proven                                                       |
| bicategory of DMCs with terminal object in the base category       | defined directly         | defined using `disp_dirprod_bicat` over `bicat_of_univ_cats` |
| univalence of bicategory of terminal DMCs                          |                          | proven using properties of displayed categories              |
| pseudofunctor into the bicategory of full comprehension categories | defined                  | defined                                                      |
