# Scripts and Snippets
This page documents a couple of useful scripts and snippets for working with coq and UniMath.

## See which files are currently being compiled with dune
You can use the following command to track which files are currently under compilation:
```coq
watch -n 0.5 "ps -ww aux | grep bin/coqc | sed 's/coqc.*UniMath UniMath /coqc ... /' | sed '/grep/d'"
```
* `watch -n 0.5` executes the command every 0.5 seconds.
* `ps` gets a list of processes.
* `grep` searches for occurrences of `bin/coqc`: the processes that we are interested in.
* `sed` replaces the very long list of flags by `...`.
* `sed` then removes the line of the `ps ... | grep ...` command, because we are not interested in that.
