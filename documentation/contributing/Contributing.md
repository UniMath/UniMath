# Contributing

## What to contribute?
Potential work on the library is tracked in two ways. Firstly, there are the [GitHub issues](https://github.com/UniMath/UniMath/issues). These keep track of proofs, definitions, or refactorings that would make working with the UniMath library easier or better, or that are needed for further work. There is also the [Opportunities](./Opportunities.md) file, which tracks projects that would be interesting to do, and are possible to do with the current state of the library, but are currently not necessary.

Feel free to take up a project from either the issues or opportunities file, or to add new issues or opportunities you think of.

## Pull Requests
The git and GitHub part of the contribution process, including forking, branching, and remote tracking, is documented on the page about [git and GitHub](./Git-and-GitHub.md).

Before making a pull request:
- Check all your modified code compiles.
- Run the sanity checks with `make sanity-checks`.
- Make sure that your code adheres to the [Style guide](./Style-guide.md). In particular, to make sure that your code is usable down the road, make sure that your proofs and definitions have the correct [opaqueness](./../guides/Opaqueness.md).
- If you have changed the file structure of the repository, for example by adding a new file, make sure you have followed the instructions below.

In the end, you will need someone from the [coordinating committee](../unimath/About-UniMath.md#coordinating-committee) to merge your pull request into the main repository. Note that from then on, your code will be subject to the [copyright and license agreement](../../LICENSE.md).

## Foundations

Changes to the package "Foundations" are normally not accepted, for we are trying to keep it in a state close to what Vladimir Voevodsky originally intended. A warning is issued if you run `make` or `make all` and have changed a file in the Foundations package.

## Adding a file to a package
To add a file to a package, add its path to `.package/files`. Each package contains a subdirectory called `.package`, with one file called `files`. This consists of a list of the paths to the `*.v` files of the package, in order: A file is listed after files it depends on. This is done so the `TAGS` file will be correctly sequenced.

## Adding a new package
Create a subdirectory of this directory, populate it with your files, add a `README.md` file, and add a file `.package/files` as described in [Adding a file to a package](#adding-a-file-to-a-package). Then add the name of your package to the head of the list assigned to `PACKAGES` in the file [`Makefile`](../../Makefile).

Alternatively, if you would like to test your package without modifying the `Makefile`, add its name to the head of the list in [`build/Makefile-configuration`](../../build/Makefile-configuration), which is created from [`build/Makefile-configuration-template`](../../build/Makefile-configuration-template).
