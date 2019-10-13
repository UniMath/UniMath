# Second method to install ocaml

This method for installing ocaml allows more flexibility, but is more involved
than the method in [INSTALL.md](./INSTALL.md), because it depends on "opam".

First install opam and needed prerequisites:

- Under Mac OS X, this is done by install "Homebrew", available from http://brew.sh/, and
  then using it to install opam with the following command.
  ```bash
  $ brew install opam gtksourceview3
  ```

- Under Ubuntu:
  ```bash
  sudo apt-get install opam libgtksourceview-3.0-dev
  ```

Then, on all systems, set up the opam system as follows.

```bash
$ opam init --bare
$ opam switch create --empty empty
$ opam install num ocamlfind lablgtk3-sourceview3
```

(We choose to ignore any ocaml compiler offered by the system, preferring to
let opam install its preferred compiler.  That avoid problems with version
skew.)

(The packages involving "gtk" are relevant only if coqide is to be built.)

Now arrange for the programs installed by opam to be available to the currently
running shell:

```bash
$ eval `opam env`
```

If you haven't done it previously in connection with installing opam, as you
have just done, arrange for the programs (such as ocamlc) that opam will
install for you to be found by your shell the next time you log in by adding
the line

```bash
$ eval `opam env`
```

to your file `~/.profile`, after any lines in the file that add
`/usr/local/bin` to the `PATH` environment variable.  (Homebrew and opam both
know how to install `ocamlc`, and we intend to use `opam` to get a version of
`ocamlc` appropriate for compiling the version of Coq used by UniMath.)

At any time, you may check that the progams installed by opam are accessible by
you as follows.

```bash
$ type ocamlc
ocamlc is hashed (/Users/XXXXXXXX/.opam/empty/bin/ocamlc)
```

A result displaying a path that doesn't pass through `.opam` indicates that the
wrong compiler is visible in the directories listed in your `PATH` environment
variable.
