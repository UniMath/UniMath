# Second method to install ocaml

This method for installing ocaml allows more flexibility, but is more involved
than the method in [INSTALL.md](./INSTALL.md), because it depends on "opam".

First install opam and needed prerequisites:

- Under Mac OS X, this is done by install "Homebrew", available from http://brew.sh/, and
  then using it to install opam with the following command.
  ```bash
  $ brew install opam gtksourceview3
  ```

  Then set up the opam system as follows.

  ```bash
  $ opam init --bare
  $ opam switch create --empty empty
  $ opam install -y num lablgtk conf-gtksourceview lablgtk3-sourceview3 camlp5
  ```

- Under Ubuntu:

  First, install "opam":
  ```bash
  sudo apt-get install -y opam
  ```

  Now check which version of opam is installed with the command `opam
  --version`.  If it is less than version 2, then we need to get opam from a
  "ppa", as follows.
  ```bash
  sudo add-apt-repository -y ppa:avsm/ppa
  sudo apt update
  sudo apt install -y opam
  ```

  (Ubuntu 18.04 comes with opam 1.2.2, whereas Ubuntu 19.04 comes with opam 2.0.3.)

  Then install needed libraries as follows.
  ```bash
  sudo apt-get install --quiet --no-install-recommends pkg-config libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev libexpat1-dev libgtk2.0-dev mccs m4 git ca-certificates camlp5 libgtksourceview2.0-dev
  ```

  Then set up the opam system as follows.

  ```bash
  $ opam init --bare
  $ opam switch create --empty empty
  $ opam install -y --solver=mccs num lablgtk conf-gtksourceview lablgtk3-sourceview3 camlp5
  ```

In both of the procedures above, we ignore any ocaml compiler offered by the
system, preferring to let opam install its preferred compiler.  That avoid
problems with version skew, which I don't understand.

The packages involving "gtk", installed above, are relevant only if coqide is
to be built.

Now arrange for the programs installed by opam to be available to the currently
running shell:

```bash
$ eval `opam env`
```

If you haven't done it previously in connection with installing opam, as you
have just done, arrange for the programs (such as ocamlc) that opam will
install for you to be found by your shell the next time you log in by also
adding the line above to your file `~/.profile`, after any lines in the file
that add `/usr/local/bin` to the `PATH` environment variable.  (Homebrew and
opam both know how to install `ocamlc`, and we intend to use `opam` to get a
version of `ocamlc` appropriate for compiling the version of Coq used by
UniMath.)

At any time, you may check that the progams installed by opam are accessible by
you as follows.

```bash
$ type ocamlc
ocamlc is hashed (/Users/XXXXXXXX/.opam/empty/bin/ocamlc)
```

A result displaying a path that doesn't pass through `.opam` indicates that the
wrong compiler is visible in the directories listed in your `PATH` environment
variable.
