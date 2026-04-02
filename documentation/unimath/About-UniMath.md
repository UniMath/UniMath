# About UniMath

* For articles that have accompanying proofs in UniMath or built upon UniMath, or articles that describe UniMath, see [Articles with formalization](./Articles-with-formalization.md).
* For events about UniMath, see the [Calendar](./Calendar.md).
* For discussions of different aspects of formalization, see [Discussions](./Discussions.md).
* For the formal language used in the UniMath project, see [Martin-Löf Type Theory](./Martin-Lof-type-theory.md).
* For a summary of various attempts to introduce resizing rules, to get rid of -type-in-type, see [Resizing Rules](./Resizing-rules.md).
* For an overview of the most important symbols used in UniMath, see [Symbols List](./Symbols-list.md).

## Citing UniMath
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

## Coordinating Committee
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
- Arnoud van der Leer
- Michael Lindgren
- Peter LeFanu Lumsdaine
- Ralph Matthes
- Niels van der Weide

## Packages
The largest two packages in the repository are CategoryTheory and Bicategories. Most of the activity in UniMath is centered around these two.

Since a part of the Bicategories is quite heavy and takes a long time to compile, we generally avoid adding code in the rest of the library that depends on Bicategories.

## The satellite repositories

The five satellites that fall within the continuous integration of this GitHub repository ([SetHITs](https://github.com/UniMath/SetHITs), [GrpdHITs](https://github.com/UniMath/GrpdHITs), [TypeTheory](https://github.com/UniMath/TypeTheory), [largecatmodules](https://github.com/UniMath/largecatmodules), [Schools](https://github.com/UniMath/Schools)) are less integrated parts of UniMath, just like the "contributions" that Coq had a long time ago. Satellites do not need to conform to the coding style of UniMath as consistently as the UniMath library itself (HITs use more inductive types). They are maintained, even if this often only means propagating upstream changes.

To download and compile a satellite repository, for example `SetHITs`, go to the root directory of the UniMath repository (so you should see a `UniMath` directory as well as a `README.md` file) and run
```bash
git clone git@github.com:UniMath/SetHITs.git
dune build SetHITs
```
You can also compile all of UniMath together with the satellites, by cloning the 4 repositories and running the compilation command:
```bash
git clone git@github.com:UniMath/SetHITs.git
git clone git@github.com:UniMath/GrpdHITs.git
git clone git@github.com:UniMath/TypeTheory.git
git clone git@github.com:UniMath/largecatmodules.git
git clone git@github.com:UniMath/Schools.git
dune build
```
Note that changes to the satellites have to be filed to their respective repositories, so you should fork the satellite repository that you are working on, make sure that your local copy has its origin set to that fork, and push to that fork. When you are done, create a pull request to the satellite repository.
