Univalent Mathematics Coq files
===============================

Each subdirectory of this directory consists of a separate package, with
various authors, as recorded in the README (or README.md) file in it.

## Contributing code to UniMath

Volunteers may look at unassigned issues at GitHub and volunteer to be assigned
one of them.  New proposals and ideas may be submitted as issues at GitHub for
discussion and feedback.

Contributions are submitted in the form of pull requests at GitHub and are
subject to approval by the UniMath Development Team.

Changes to the package "Foundations" are normally not accepted, for we are
trying to keep it in a state close to what Vladimir Voevodsky originally
intended.  A warning is issued if you run `make` or `make all` and have changed
a file in the Foundations package.

## The UniMath formal language

The formal language used in the UniMath project is based on Martin-Löf type
theory, as present in MLTT79 below.  We are currently on version 2.

UniMath-1 is MLTT79 except:

- the bound variable in a λ-expression is annotated with its type
- we omit W-types
- just the finite types of cardinality 0, 1, and 2 are used, although there would be no problem with introducing further ones
- we omit reflection from identities to judgmental equalities
- we add the resizing rules from the [slides](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf) of Voevodsky's 2011 talk in Bergen

UniMath-2 is UniMath-1 except:

- we add η for pairs

The axioms accepted are: the univalence axiom, the law of excluded middle, the
axiom of choice, and a few new variants of the axiom of choice, validated by
the semantic model.

MLTT79 is this paper:
```
@incollection {MLTT79,
    AUTHOR = {Martin-L\"of, Per},
     TITLE = {Constructive mathematics and computer programming},
 BOOKTITLE = {Logic, methodology and philosophy of science, {VI} ({H}annover, 1979)},
    SERIES = {Stud. Logic Found. Math.},
    VOLUME = {104},
     PAGES = {153--175},
 PUBLISHER = {North-Holland, Amsterdam},
      YEAR = {1982},
   MRCLASS = {03F50 (03B70 03F55 68Q45)},
  MRNUMBER = {682410},
MRREVIEWER = {B. H. Mayoh},
       DOI = {10.1016/S0049-237X(09)70189-2},
       URL = {http://dx.doi.org/10.1016/S0049-237X(09)70189-2},
}
```