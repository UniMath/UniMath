[![DOI](https://zenodo.org/badge/17321421.svg)](https://zenodo.org/badge/latestdoi/17321421)

Univalent Mathematics
=====================

This [Coq](https://coq.inria.fr/) library aims to formalize a substantial body of mathematics using the
[univalent point of view](https://en.wikipedia.org/wiki/Univalent_foundations).


Trying out UniMath
------------------

You can try out UniMath in the browser by clicking [here](https://unimath.github.io/live/).
For instance, you can run the files from the [School on Univalent Mathematics](https://unimath.github.io/Schools/) in the browser.


Using UniMath on your computer
------------------------------

To install UniMath on your computer, there are two options:

- Install a released binary version of UniMath via the [Coq Platform](https://coq.inria.fr/download).
- To develop, and contribute to, UniMath, you should compile the latest version of UniMath yourself - see [INSTALL.md](https://github.com/UniMath/UniMath/blob/master/INSTALL.md).


Usage
-----

See [USAGE.md](./USAGE.md)

Contents
--------

The [UniMath subdirectory](UniMath/) contains various packages of formalized
mathematics. For more information, see the [UniMath Table of Contents](UniMath/CONTENTS.md).

Some scientific articles describing the contents of the UniMath library or work using it are listed in the 
[wiki](https://github.com/UniMath/UniMath/wiki/Articles-with-accompanying-formalization-in-UniMath).

Contributing to UniMath
-----------------------

To contribute to UniMath, submit a pull request.  Your code will be subject to the 
copyright and license agreement in [LICENSE.md](LICENSE.md).

For the style guide and other instructions, see [UniMath/README.md](UniMath/README.md).

Discussing UniMath & Getting Help
---------------------------------

- **Questions** about the UniMath library, compilation, and installation of UniMath, etc.,
can be asked in the [UniMath Zulip](https://unimath.zulipchat.com) (click [here](https://unimath.zulipchat.com/register/) to register)
or on the [UniMath mailing list](mailto:univalent-mathematics@googlegroups.com) (archived in a [Google Group](https://groups.google.com/forum/#!forum/univalent-mathematics)).
- **Bugs** should be reported in our [UniMath bug tracker on GitHub](https://github.com/UniMath/UniMath/issues).


Citing UniMath
--------------

To cite UniMath in your article, you can use the following bibtex item:
```bibtex
@Misc{UniMath,
    author = {Voevodsky, Vladimir and Ahrens, Benedikt and Grayson, Daniel and others},
    title = {UniMath --- a computer-checked library of univalent mathematics},
    url = {https://github.com/UniMath/UniMath},
    howpublished = {available at \url{http://unimath.org}},
    doi          = {10.5281/zenodo.10849216},
    url          = {https://doi.org/10.5281/zenodo.10849216}
 }
```
Note that this requires ```\usepackage{url}``` or ```\usepackage{hyperref}```.


The UniMath Coordinating Committee
----------------------------

The UniMath project was started in 2014 by merging the repository
[Foundations](https://github.com/UniMath/Foundations), by Vladimir Voevodsky
(written in 2010), with two repositories based on it:
[rezk_completion](https://github.com/benediktahrens/rezk_completion), by
Benedikt Ahrens, and [Ktheory](https://github.com/DanGrayson/Ktheory), by
Daniel Grayson.  Vladimir Voevodsky was a member of the team until his death in
September, 2017.

The current members of the UniMath Coordinating Committee are:

- Benedikt Ahrens
- Daniel Grayson
- Michael Lindgren
- Peter LeFanu Lumsdaine
- Ralph Matthes
- Niels van der Weide

Acknowledgments
---------------

The UniMath development team gratefully acknowledges the great work by
the Coq development team in providing the [Coq proof assistant](https://coq.inria.fr/), as well
as their support in keeping UniMath compatible with Coq.
