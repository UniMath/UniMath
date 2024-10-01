# Contributing

Contributions are submitted in the form of pull requests on GitHub and are
subject to approval by the UniMath Development Team. Your code will be subject to the 
copyright and license agreement in [LICENSE.md](LICENSE.md).

Changes to the package "Foundations" are normally not accepted, for we are
trying to keep it in a state close to what Vladimir Voevodsky originally
intended.  A warning is issued if you run `make` or `make all` and have changed
a file in the Foundations package.

The git/github part of the contribution process is documented in [Making a Pull Request](Making-a-pull-request), including forking, branching, and remote tracking. Before you make the pull-request, ensure you've read the rest of this guide.

## Making changes

Important info:
- [Style-Guide](./Style-guide.md) - rules, naming conventions, code structure, comments, etc
- [On opaqueness](./On-opaqueness.md) - making proofs of propositions opaque

Pages that may be useful:
- [Tactics and tricks](./Tactics-and-tricks)
- [The standard API for a type](./The-standard-API-for-a-type)
- [My proof is slow](./My-proof-is-slow)
- [About UniMath](./About-UniMath)
- [Resources for new users](./Resources-for-new-users.md)

## Adding a file to a package

Each package contains a subdirectory called ".package".  The file
".packages/files" consists of a list of the paths to the *.v files of the
package, in order, i.e., a file is listed after files it depends on.
(That's just so the TAGS file will be correctly sequenced.)  To add a file to a
package, add its path to that file.

## Adding a new package

Create a subdirectory of this directory, populate it with your files, add a
README (or README.md) file, and add a file .package/files, listing the *.v
files of your package, as above.  Then add the name of your package to the head
of the list assigned to "PACKAGES" in the file "./Makefile", or, alternatively,
if you'd like to test your package without modifying "./Makefile", which you might
accidentally commit and push, add its name to the head of the list in
"../build/Makefile-configuration", which is created from
"../build/Makefile-configuration-template".

## Run sanity checks

```bash
make sanity-checks
```