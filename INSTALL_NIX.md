Building UniMath with Nix
=====================================

## Introduction

These are instructions to install UniMath on a Unix-like system using
the Nix Package Manager.

This method has some advantages:
1. Should work both on Mac and on any major Linux distribution without
   any difference.
2. Does not require to install OCaml or Git or other dependencies
   separately (only Nix itself).
3. Does not interfere with or modify other software already present on
   the same system (other versions of OCaml, camlp5, etc).
4. It makes possible to uninstall cleanly all the software.

The main disadvantage of this method is that it is not the most used
(see [INSTALL.md](https://github.com/UniMath/UniMath/blob/master/INSTALL.md))
and it is not very well tested at the moment.

## Installation step-by-step

1. If you already have the Nix Package Manager installed, skip this step.
   Otherwise, type the following command to install Nix
   (as a user other than root):
   ```bash
   $ curl https://nixos.org/nix/install | sh
   ```
   Follow the instructions output by the script.
   The installation script requires that you have sudo access to `root`.
   (Go to the [NixOS website](https://nixos.org) to get
   [more detailed instructions](https://nixos.org/nix/download.html).)
2. Start a "nix-shell" with the following command:
   ```bash
   $ nix-shell -p ocaml ocamlPackages.findlib ocamlPackages.camlp4 ocamlPackages.camlp5 ocamlPackages.num gnumake git
   ```
   (This may require some time to download and deploy the ocaml
   environment into the Nix storage.)
3. Clone UniMath, move to the top directory and launch the build:
   ```bash
   $ git clone https://github.com/UniMath/UniMath.git
   $ cd UniMath
   $ make
   ```
   Once the building is finished, you can quit the nix-shell (type `exit`).
4. You may also want to install emacs using Nix:
   ```bash
   $ nix-env -i emacs
   ```
   (Or skip this step if you have emacs already installed.)
5. Finally, you need to install Proof-General following the instructions
   on the [website](https://proofgeneral.github.io).

## How to uninstall UniMath and its dependencies

If you want to uninstall UniMath and OCaml to reclaim disk space:
1. Delete the UniMath directory:
   ```bash
   $ rm -rf UniMath
   ```
2. Purge the software installed with Nix:
   ```
   $ nix-collect-garbage
   ```

If you want to uninstall the Nix Package Manager directly, consult the
[Nix Manual](https://nixos.org/nix/manual/#chap-installation).
