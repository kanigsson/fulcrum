# Fulcrum implementation and proof in SPARK

[![Build Status](https://travis-ci.com/kanigsson/fulcrum.svg?branch=master)](https://travis-ci.com/kanigsson/fulcrum)

This small example shows the implementation and proof of the so-called Fulcrum in SPARK, to
answer the third problem of this [challenge](https://hillelwayne.com/post/theorem-prover-showdown/).

You can verify the proof using [SPARK](https://www.adacore.com/sparkpro) as
follows:

```bash

$ gnatprove -P fulcrum --report=all --level=2

```

and compile and run the simple test case as follows using [GNAT
Pro](https://www.adacore.com/gnatpro):


```bash

$ gprbuild -p -P fulcrum
$ ./obj/test_fulcrum

```
