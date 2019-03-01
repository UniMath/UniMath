# Second method to install ocaml on Mac OS X

This method allows more flexibility, but is more involved than the method in [INSTALL.md](./INSTALL.md).

Install "Homebrew", available from http://brew.sh/.

Using Homebrew, install opam with the following command:

```bash
$ brew install bash opam gtk+
$ opam init --no-setup --compiler=4.02.3
$ opam install --yes lablgtk camlp5 ocamlfind num
```

(We choose version 4.02.3 of ocamlc above, because it can successfully compile
Coq 8.6.1.)

Now arrange for the programs installed by opam to be available to the currently
running shell:

```bash
$ eval `opam config env`
```

If you haven't done it previously in connection with installing opam, as you
have just done, arrange for the programs (such as ocamlc) that opam will
install for you to be found by your shell, the next time you log in, by adding
the line

```bash
$ eval `opam config env`
```

to your file `~/.profile`, after any lines in the file that add
`/usr/local/bin` to the `PATH` environment variable.  (Homebrew and opam both
know how to install `ocamlc`, and we intend to use `opam` to get a version of
`ocamlc` appropriate for compiling the version of Coq used by UniMath.)

The next time you log in, or now, you may check that the progams installed by
opam are accessible by you as follows.

```bash
$ type ocamlc
ocamlc is hashed (/Users/XXXXXXXX/.opam/4.02.3/bin/ocamlc)
$ ocamlc -version
4.02.3
$ camlp5 -v
Camlp5 version 7.03 (ocaml 4.02.3)
```
