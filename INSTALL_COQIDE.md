Installing CoqIDE
=================

If you wish also to build the program `coqide`, then issue the following
command.

```bash
$ make BUILD_COQIDE=yes
```

Alternatively, you can specify the value of the BUILD_COQIDE option more
permanently by following the instructions in the file
build/Makefile-configuration-template.

Later on, after running the command `make install` as instructed below, in
order to run the program `coqide`, you may use the following command.

```bash
$ sub/coq/bin/coqide <flags>
```
where `<flags>` are the options passed to Coq as per the [Emacs configuration file](./UniMath/.dir-locals.el.in).
