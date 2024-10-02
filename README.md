[![DOI](https://zenodo.org/badge/17321421.svg)](https://zenodo.org/badge/latestdoi/17321421)

Univalent Mathematics
=====================

This [Coq](https://coq.inria.fr/) library aims to formalize a substantial body of mathematics using the
[univalent point of view](https://en.wikipedia.org/wiki/Univalent_foundations).

Discussing UniMath & Getting Help
---------------------------------

- For **questions** about the UniMath library and **requests** for **help** with installing, compiling or using the library, visit the [UniMath Zulip](https://unimath.zulipchat.com) (click [here](https://unimath.zulipchat.com/register/) to register).
- For **bugs** and **suggestions** about **improvements**, file an [issue on GitHub](https://github.com/UniMath/UniMath/issues).


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

See the documentation about [contributing](documentation/contributing/contributing.md)


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
