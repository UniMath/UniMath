MoreFoundations
===============

This package is a repository for auxiliary material at a basic level, such as
in the package "Foundations", which doesn't fit into one of the large
categories represented by a later package.  The material in this package is
envisioned as being generally useful in any of the other later packages, so it
comes second on the list of of packages in the Makefile.

The file Foundations.v loads all of the files of Foundations and exports them,
for use by the files in this package.

The file All.v loads and exports all the files of Foundations and all the files
in this package, later packages can get everything by importing it.

